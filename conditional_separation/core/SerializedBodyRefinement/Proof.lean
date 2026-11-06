import SerializedBody.Target
namespace SerializedBodyRefinement
open Pnp3.Complexity.Uniform.V1
-- Proof-side Nat-address paths, adapted freshly; no donor private term lookup.
-- One Edge is proved equal to one actual frozen SerializedBody.machine step.
private structure Node where
  state : Fin 7500
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {N B : Nat} (c : Node) (h : c.head  <  tapeLength N B) : Config 7500 N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (P : Nat) (c d : Node) : Prop where
  nonterminal : 4  ≤  c.state.val
  before : c.head    ≤    P
  after : d.head    ≤    P
  row : (SerializedBody.machine.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (SerializedBody.machine.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (SerializedBody.machine.step c.state (c.tape c.head)).2.1
private inductive Path (P : Nat) : Nat → Node → Node → Prop
  | nil (c) (h : c.head    ≤    P) : Path P 0 c c
  | cons {t c d e} : Edge P c d → Path P t d e → Path P (t+1) c e
namespace Path
private theorem bounds {P t c d} (h : Path P t c d) : c.head    ≤    P ∧ d.head    ≤    P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {P t u c d e} (h : Path P t c d) (g : Path P u d e) :
    Path P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {N B P t c d} (h : Path P t c d) (hp : P  <  tapeLength N B) :
    SerializedBody.machine.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge P c d) :
      SerializedBody.machine.stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ (SerializedBody.machine.step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : (SerializedBody.machine.step c.state (c.tape c.head)).2.2 with
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
      SerializedBody.machine.run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; simp only [UniformTM.run]
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,SerializedBody.machine.run_add]
    rw [show SerializedBody.machine.run 1 (embed c hc)=SerializedBody.machine.stepConfig (embed c hc) by simp only [UniformTM.run]]
    rw [step ed]
    exact ih _ _
end Path
private theorem hop {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hb : h    ≤    P) (ha : h'    ≤    P)
    (safe : 4  ≤  s.val)
    (row : SerializedBody.machine.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨safe,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h  <;> simp [put,hi]
private theorem keep {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hb : h    ≤    P) (ha : h'    ≤    P)
    (safe : 4  ≤  s.val)
    (row : SerializedBody.machine.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hb ha safe row hm
  rwa [put_same] at one
private theorem sweepR {P : Nat} (s : Fin 7500) (T : Nat → Option Bool) (h r : Nat) (fit : h+r    ≤    P) (safe : 4  ≤  s.val) (rows : ∀ i, h    ≤    i → i  <  h+r → SerializedBody.machine.step s (T i)=(s,T i,.right)) :
    Path P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right (P := P) (by omega) (by omega) safe (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {P : Nat} (s : Fin 7500) (T : Nat → Option Bool) (low r : Nat) (fit : low+r    ≤    P) (safe : 4  ≤  s.val) (rows : ∀ i, low  <  i → i    ≤    low+r → SerializedBody.machine.step s (T i)=(s,T i,.left)) :
    Path P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega) safe (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest

private theorem crossR {P : Nat} (e s q : Fin 7500) (T : Nat → Option Bool)
    (a w : Nat) (fit : a+w+1  ≤  P) (safeE : 4  ≤  e.val) (safeS : 4  ≤  s.val)
    (atA : T a=none) (atB : T (a+w+1)=none)
    (cells : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (start : SerializedBody.machine.step e none=(s,none,.right))
    (loop : ∀ b, SerializedBody.machine.step s (some b)=(s,some b,.right))
    (stop : SerializedBody.machine.step s none=(q,none,.stay)) :
    Path P (w+2) ⟨e,a,T⟩ ⟨q,a+w+1,T⟩ := by
  have one:=keep e s a (a+1) T .right (P:=P) (by omega) (by omega) safeE (by rw [atA]; exact start) rfl
  have middle:=sweepR s T (a+1) w (P:=P) (by omega) safeS (by
    intro i lo hi
    obtain ⟨b,hb⟩:=cells i (by omega) (by omega)
    rw [hb]; exact loop b)
  rw [show a+1+w=a+w+1 by omega] at middle
  have last:=keep s q (a+w+1) (a+w+1) T .stay (P:=P) fit fit safeS (by rw [atB]; exact stop) rfl
  have path:=one.append (middle.append last)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem crossL {P : Nat} (e s q : Fin 7500) (T : Nat → Option Bool)
    (a w : Nat) (fit : a+w+1  ≤  P) (safeE : 4  ≤  e.val) (safeS : 4  ≤  s.val)
    (atA : T a=none) (atB : T (a+w+1)=none)
    (cells : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (start : SerializedBody.machine.step e none=(s,none,.left))
    (loop : ∀ b, SerializedBody.machine.step s (some b)=(s,some b,.left))
    (stop : SerializedBody.machine.step s none=(q,none,.stay)) :
    Path P (w+2) ⟨e,a+w+1,T⟩ ⟨q,a,T⟩ := by
  have one:=keep e s (a+w+1) (a+w) T .left (P:=P) fit (by omega) safeE (by rw [atB]; exact start) (by simp [dest])
  have middle:=sweepL s T a w (P:=P) (by omega) safeS (by
    intro i lo hi
    obtain ⟨b,hb⟩:=cells i lo (by omega)
    rw [hb]; exact loop b)
  have last:=keep s q a a T .stay (P:=P) (by omega) (by omega) safeS (by rw [atA]; exact stop) rfl
  have path:=one.append (middle.append last)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
-- Finite proof certificates for literal delimiter-crossing control routes.
-- No certificate is runtime data; each row field is a kernel equality of the SAME table.
private inductive RouteR : Nat → Nat → Fin 7500 → Fin 7500 → Prop
  | nil (i q) : RouteR i i q q
  | next {i j e s q x} : 4 ≤ e.val → 4 ≤ s.val →
      SerializedBody.machine.step e none=(s,none,.right) →
      (∀ b, SerializedBody.machine.step s (some b)=(s,some b,.right)) →
      SerializedBody.machine.step s none=(q,none,.stay) →
      RouteR (i+1) j q x → RouteR i j e x
private inductive RouteL : Nat → Nat → Fin 7500 → Fin 7500 → Prop
  | nil (i q) : RouteL i i q q
  | next {i j e s q x} : 4 ≤ e.val → 4 ≤ s.val →
      SerializedBody.machine.step e none=(s,none,.left) →
      (∀ b, SerializedBody.machine.step s (some b)=(s,some b,.left)) →
      SerializedBody.machine.step s none=(q,none,.stay) →
      RouteL i j q x → RouteL (i+1) j e x
private theorem RouteR.span {i j e x} (h : RouteR i j e x) : i ≤ j := by
  induction h with | nil => exact le_rfl | next _ _ _ _ _ _ ih => omega
private theorem RouteL.span {i j e x} (h : RouteL i j e x) : j ≤ i := by
  induction h with | nil => exact le_rfl | next _ _ _ _ _ _ ih => omega
private theorem RouteR.execute {i j e x P} (h : RouteR i j e x)
    (D : Nat → Nat) (T : Nat → Option Bool) (fit : D j ≤ P)
    (rise : ∀ k, i ≤ k → k < j → D k < D (k+1))
    (mono : ∀ a b, i ≤ a → a ≤ b → b ≤ j → D a ≤ D b)
    (blank : ∀ k, i ≤ k → k ≤ j → T (D k)=none)
    (cells : ∀ k u, i ≤ k → k < j → D k < u → u < D (k+1) → ∃ b,T u=some b) :
    Path P (D j-D i+(j-i)) ⟨e,D i,T⟩ ⟨x,D j,T⟩ := by
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
private theorem RouteL.execute {i j e x P} (h : RouteL i j e x)
    (D : Nat → Nat) (T : Nat → Option Bool) (fit : D i ≤ P)
    (rise : ∀ k, j ≤ k → k < i → D k < D (k+1))
    (mono : ∀ a b, j ≤ a → a ≤ b → b ≤ i → D a ≤ D b)
    (blank : ∀ k, j ≤ k → k ≤ i → T (D k)=none)
    (cells : ∀ k u, j ≤ k → k < i → D k < u → u < D (k+1) → ∃ b,T u=some b) :
    Path P (D i-D j+(i-j)) ⟨e,D i,T⟩ ⟨x,D j,T⟩ := by
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
  rise : ∀ j, j < 12 → D j < D (j+1)
  mono : ∀ a b, a ≤ b → b ≤ 12 → D a ≤ D b
  blank : ∀ j, j ≤ 12 → T (D j)=none
  cells : ∀ j i, j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b
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
private theorem Grid.goR {D T i j s q P} (g : Grid D T) (r : RouteR i j s q)
    (hj : j ≤ 12) (fit : D 12 ≤ P) :
    Path P (D j-D i+(j-i)) ⟨s,D i,T⟩ ⟨q,D j,T⟩ :=
  r.execute D T (le_trans (g.mono _ _ hj le_rfl) fit)
    (by intro k _ hi; exact g.rise k (by omega))
    (by intro a b _ ab bj; exact g.mono a b ab (by omega))
    (by intro k _ hi; exact g.blank k (by omega))
    (by intro k u _ hi lo up; exact g.cells k u (by omega) lo up)
private theorem Grid.goL {D T i j s q P} (g : Grid D T) (r : RouteL i j s q)
    (hi : i ≤ 12) (fit : D 12 ≤ P) :
    Path P (D i-D j+(i-j)) ⟨s,D i,T⟩ ⟨q,D j,T⟩ :=
  r.execute D T (le_trans (g.mono _ _ hi le_rfl) fit)
    (by intro k _ hk; exact g.rise k (by omega))
    (by intro a b _ ab bi; exact g.mono a b ab (by omega))
    (by intro k _ hk; exact g.blank k (by omega))
    (by intro k u _ hk lo up; exact g.cells k u (by omega) lo up)
private def Unary (D : Nat → Nat) (T : Nat → Option Bool) (j v : Nat) : Prop :=
  ∀ i, D j < i → i < D (j+1) → T i=some (decide (i-D j ≤ v))
private def DecRows (j : Nat) (start zero pos : Fin 7500) : Prop :=
  ∃ e s t l zr pr : Fin 7500, 4 ≤ e.val ∧ 4 ≤ s.val ∧ 4 ≤ t.val ∧ 4 ≤ l.val ∧
    RouteR 0 j start e ∧ RouteL j 0 zr zero ∧ RouteL j 0 pr pos ∧
    SerializedBody.machine.step e none=(s,none,.right) ∧
    SerializedBody.machine.step s (some true)=(s,some true,.right) ∧
    (∀ b, b≠some true → SerializedBody.machine.step s b=(t,b,.left)) ∧
    SerializedBody.machine.step t none=(zr,none,.stay) ∧
    SerializedBody.machine.step t (some true)=(l,some false,.stay) ∧
    (∀ b, SerializedBody.machine.step l (some b)=(l,some b,.left)) ∧
    SerializedBody.machine.step l none=(pr,none,.stay)
private theorem unary_true {D T j v w} (h : Unary D T j v)
    (len : D (j+1)=D j+w+1) (hv : v ≤ w) {i : Nat}
    (lo : D j < i) (hi : i ≤ D j+v) : T i=some true := by
  rw [h i lo (by omega)]
  simp [show i-D j ≤ v by omega]
private theorem unary_boundary {D T j v w} (grid : Grid D T) (h : Unary D T j v)
    (hj : j < 12) (len : D (j+1)=D j+w+1) (hv : v ≤ w) :
    T (D j+v+1)≠some true := by
  by_cases full : v=w
  · rw [full,← len,grid.blank _ (by omega)]; simp
  · rw [h _ (by omega) (by omega)]
    simp [show ¬D j+v+1-D j ≤ v by omega]
private theorem dec_positive {D T j w v P start zero pos} (grid : Grid D T)
    (hj : j < 12) (fit : D 12 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j v) (positive : 0 < v) (small : v ≤ w)
    (code : DecRows j start zero pos) :
    Path P (2*(D j-D 0+j)+2*v+4) ⟨start,D 0,T⟩
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
  have take:=hop t l (D j+v) (D j+v) T (some false) .stay (P:=P) (by omega) (by omega) st (by rw [val]; exact rt1) rfl
  have retreat:=sweepL l U (D j) v (P:=P) (by omega) sl (by
    intro i lo hi
    obtain ⟨b,hb⟩:=gu.cells j i hj lo (by omega)
    rw [hb]; exact rl b)
  have exit:=keep l pr (D j) (D j) U .stay (P:=P) (by omega) (by omega) sl (by rw [gu.blank j (by omega)]; exact rn) rfl
  have whole:=(grid.goR out (by omega) fit).append (entry.append (sweep.append (back.append (take.append (retreat.append (exit.append (gu.goL rp (by omega) fit)))))))
  convert whole using 1
  omega

private theorem dec_zero {D T j w P start zero pos} (grid : Grid D T)
    (hj : j < 12) (fit : D 12 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j 0) (code : DecRows j start zero pos) :
    Path P (2*(D j-D 0+j)+3) ⟨start,D 0,T⟩ ⟨zero,D 0,T⟩ := by
  rcases code with ⟨e,s,t,l,zr,pr,se,ss,st,sl,out,rz,rp,re,rs,rb,rt0,rt1,rl,rn⟩
  have room : D j+1 ≤ P := le_trans (show D j+1 ≤ D (j+1) by omega)
    (le_trans (grid.mono (j+1) 12 (by omega) le_rfl) fit)
  have entry:=keep e s (D j) (D j+1) T .right (P:=P) (by omega) room se (by rw [grid.blank j (by omega)]; exact re) rfl
  have back:=keep s t (D j+1) (D j) T .left (P:=P) room (by omega) ss
    (rb _ (by simpa using unary_boundary grid unary hj len (Nat.zero_le w))) (by simp [dest])
  have take:=keep t zr (D j) (D j) T .stay (P:=P) (by omega) (by omega) st (by rw [grid.blank j (by omega)]; exact rt0) rfl
  have whole:=(grid.goR out (by omega) fit).append (entry.append (back.append (take.append (grid.goL rz (by omega) fit))))
  convert whole using 1
  omega
private def IncRows (j : Nat) (start out : Fin 7500) : Prop :=
  ∃ e s l pr : Fin 7500, 4 ≤ e.val ∧ 4 ≤ s.val ∧ 4 ≤ l.val ∧
    RouteR 0 j start e ∧ RouteL j 0 pr out ∧
    SerializedBody.machine.step e none=(s,none,.right) ∧
    SerializedBody.machine.step s (some true)=(s,some true,.right) ∧
    SerializedBody.machine.step s (some false)=(l,some true,.stay) ∧
    (∀ b, SerializedBody.machine.step l (some b)=(l,some b,.left)) ∧
    SerializedBody.machine.step l none=(pr,none,.stay)
private theorem inc_success {D T j w v P start out} (grid : Grid D T)
    (hj : j < 12) (fit : D 12 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j v) (small : v < w) (code : IncRows j start out) :
    Path P (2*(D j-D 0+j)+2*v+4) ⟨start,D 0,T⟩
      ⟨out,D 0,put T (D j+v+1) (some true)⟩ := by
  rcases code with ⟨e,s,l,pr,se,ss,sl,route,back,re,rs,rt,rl,rn⟩
  have inRoom : D j+v+1 ≤ P := le_trans (show D j+v+1 ≤ D (j+1) by omega)
    (le_trans (grid.mono (j+1) 12 (by omega) le_rfl) fit)
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
  have take:=hop s l (D j+v+1) (D j+v+1) T (some true) .stay (P:=P) inRoom inRoom ss (by rw [val]; exact rt) rfl
  have retreat:=sweepL l U (D j) (v+1) (P:=P) (by omega) sl (by
    intro i lo hi
    obtain ⟨b,hb⟩:=gu.cells j i hj lo (by omega)
    rw [hb]; exact rl b)
  rw [show D j+(v+1)=D j+v+1 by omega] at retreat
  have exit:=keep l pr (D j) (D j) U .stay (P:=P) (by omega) (by omega) sl (by rw [gu.blank j (by omega)]; exact rn) rfl
  have whole:=(grid.goR route (by omega) fit).append (entry.append (sweep.append (take.append (retreat.append (exit.append (gu.goL back (by omega) fit))))))
  convert whole using 1
  omega
private def st (i : Nat) : Fin 7500 := ⟨i%7500,Nat.mod_lt _ (by decide)⟩

section LiteralRows
set_option maxRecDepth 4000
private theorem route0 : RouteR 0 4 (st 450) (st 442) :=
  (RouteR.next (s:=(st 449)) (q:=(st 448)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 447)) (q:=(st 446)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 445)) (q:=(st 444)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 443)) (q:=(st 442)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 442))))))

private theorem route1 : RouteL 4 0 (st 292) (st 270) :=
  (RouteL.next (s:=(st 291)) (q:=(st 290)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 289)) (q:=(st 288)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 287)) (q:=(st 286)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 285)) (q:=(st 270)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 270))))))

private theorem route2 : RouteL 4 0 (st 439) (st 430) :=
  (RouteL.next (s:=(st 438)) (q:=(st 437)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 436)) (q:=(st 435)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 434)) (q:=(st 433)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 432)) (q:=(st 430)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 430))))))

private theorem dec0 : DecRows 4 (st 450) (st 270) (st 430) := by
  exact ⟨(st 442),(st 431),(st 441),(st 440),(st 292),(st 439),by decide,by decide,by decide,by decide,route0,route1,route2,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route3 : RouteR 0 11 (st 430) (st 408) :=
  (RouteR.next (s:=(st 429)) (q:=(st 428)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 427)) (q:=(st 426)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 425)) (q:=(st 424)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 423)) (q:=(st 422)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 421)) (q:=(st 420)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 419)) (q:=(st 418)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 417)) (q:=(st 416)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 415)) (q:=(st 414)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 413)) (q:=(st 412)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 411)) (q:=(st 410)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 409)) (q:=(st 408)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 408)))))))))))))

private theorem route4 : RouteL 11 0 (st 393) (st 371) :=
  (RouteL.next (s:=(st 392)) (q:=(st 391)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 390)) (q:=(st 389)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 388)) (q:=(st 387)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 386)) (q:=(st 385)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 384)) (q:=(st 383)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 382)) (q:=(st 381)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 380)) (q:=(st 379)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 378)) (q:=(st 377)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 376)) (q:=(st 375)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 374)) (q:=(st 373)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 372)) (q:=(st 371)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 371)))))))))))))

private theorem inc0 : IncRows 11 (st 430) (st 371) := by
  exact ⟨(st 408),(st 407),(st 394),(st 393),by decide,by decide,by decide,route3,route4,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route5 : RouteR 0 4 (st 552) (st 544) :=
  (RouteR.next (s:=(st 551)) (q:=(st 550)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 549)) (q:=(st 548)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 547)) (q:=(st 546)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 545)) (q:=(st 544)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 544))))))

private theorem route6 : RouteL 4 0 (st 541) (st 532) :=
  (RouteL.next (s:=(st 540)) (q:=(st 539)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 538)) (q:=(st 537)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 536)) (q:=(st 535)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 534)) (q:=(st 532)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 532))))))

private theorem dec1 : DecRows 4 (st 552) (st 270) (st 532) := by
  exact ⟨(st 544),(st 533),(st 543),(st 542),(st 292),(st 541),by decide,by decide,by decide,by decide,route5,route1,route6,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route7 : RouteR 0 11 (st 532) (st 510) :=
  (RouteR.next (s:=(st 531)) (q:=(st 530)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 529)) (q:=(st 528)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 527)) (q:=(st 526)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 525)) (q:=(st 524)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 523)) (q:=(st 522)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 521)) (q:=(st 520)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 519)) (q:=(st 518)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 517)) (q:=(st 516)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 515)) (q:=(st 514)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 513)) (q:=(st 512)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 511)) (q:=(st 510)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 510)))))))))))))

private theorem route8 : RouteL 11 0 (st 507) (st 485) :=
  (RouteL.next (s:=(st 506)) (q:=(st 505)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 504)) (q:=(st 503)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 502)) (q:=(st 501)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 500)) (q:=(st 499)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 498)) (q:=(st 497)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 496)) (q:=(st 495)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 494)) (q:=(st 493)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 492)) (q:=(st 491)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 490)) (q:=(st 489)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 488)) (q:=(st 487)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 486)) (q:=(st 485)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 485)))))))))))))

private theorem inc1 : IncRows 11 (st 532) (st 485) := by
  exact ⟨(st 510),(st 509),(st 508),(st 507),by decide,by decide,by decide,route7,route8,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route9 : RouteR 0 4 (st 654) (st 646) :=
  (RouteR.next (s:=(st 653)) (q:=(st 652)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 651)) (q:=(st 650)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 649)) (q:=(st 648)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 647)) (q:=(st 646)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 646))))))

private theorem route10 : RouteL 4 0 (st 643) (st 634) :=
  (RouteL.next (s:=(st 642)) (q:=(st 641)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 640)) (q:=(st 639)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 638)) (q:=(st 637)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 636)) (q:=(st 634)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 634))))))

private theorem dec2 : DecRows 4 (st 654) (st 270) (st 634) := by
  exact ⟨(st 646),(st 635),(st 645),(st 644),(st 292),(st 643),by decide,by decide,by decide,by decide,route9,route1,route10,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route11 : RouteR 0 11 (st 634) (st 612) :=
  (RouteR.next (s:=(st 633)) (q:=(st 632)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 631)) (q:=(st 630)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 629)) (q:=(st 628)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 627)) (q:=(st 626)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 625)) (q:=(st 624)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 623)) (q:=(st 622)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 621)) (q:=(st 620)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 619)) (q:=(st 618)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 617)) (q:=(st 616)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 615)) (q:=(st 614)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 613)) (q:=(st 612)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 612)))))))))))))

private theorem route12 : RouteL 11 0 (st 609) (st 587) :=
  (RouteL.next (s:=(st 608)) (q:=(st 607)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 606)) (q:=(st 605)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 604)) (q:=(st 603)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 602)) (q:=(st 601)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 600)) (q:=(st 599)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 598)) (q:=(st 597)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 596)) (q:=(st 595)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 594)) (q:=(st 593)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 592)) (q:=(st 591)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 590)) (q:=(st 589)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 588)) (q:=(st 587)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 587)))))))))))))

private theorem inc2 : IncRows 11 (st 634) (st 587) := by
  exact ⟨(st 612),(st 611),(st 610),(st 609),by decide,by decide,by decide,route11,route12,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route13 : RouteR 0 4 (st 756) (st 748) :=
  (RouteR.next (s:=(st 755)) (q:=(st 754)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 753)) (q:=(st 752)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 751)) (q:=(st 750)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 749)) (q:=(st 748)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 748))))))

private theorem route14 : RouteL 4 0 (st 745) (st 736) :=
  (RouteL.next (s:=(st 744)) (q:=(st 743)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 742)) (q:=(st 741)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 740)) (q:=(st 739)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 738)) (q:=(st 736)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 736))))))

private theorem dec3 : DecRows 4 (st 756) (st 270) (st 736) := by
  exact ⟨(st 748),(st 737),(st 747),(st 746),(st 292),(st 745),by decide,by decide,by decide,by decide,route13,route1,route14,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route15 : RouteR 0 11 (st 736) (st 714) :=
  (RouteR.next (s:=(st 735)) (q:=(st 734)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 733)) (q:=(st 732)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 731)) (q:=(st 730)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 729)) (q:=(st 728)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 727)) (q:=(st 726)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 725)) (q:=(st 724)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 723)) (q:=(st 722)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 721)) (q:=(st 720)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 719)) (q:=(st 718)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 717)) (q:=(st 716)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 715)) (q:=(st 714)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 714)))))))))))))

private theorem route16 : RouteL 11 0 (st 711) (st 689) :=
  (RouteL.next (s:=(st 710)) (q:=(st 709)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 708)) (q:=(st 707)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 706)) (q:=(st 705)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 704)) (q:=(st 703)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 702)) (q:=(st 701)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 700)) (q:=(st 699)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 698)) (q:=(st 697)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 696)) (q:=(st 695)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 694)) (q:=(st 693)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 692)) (q:=(st 691)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 690)) (q:=(st 689)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 689)))))))))))))

private theorem inc3 : IncRows 11 (st 736) (st 689) := by
  exact ⟨(st 714),(st 713),(st 712),(st 711),by decide,by decide,by decide,route15,route16,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route17 : RouteR 0 4 (st 1107) (st 1099) :=
  (RouteR.next (s:=(st 1106)) (q:=(st 1105)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1104)) (q:=(st 1103)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1102)) (q:=(st 1101)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1100)) (q:=(st 1099)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 1099))))))

private theorem route18 : RouteL 4 0 (st 1096) (st 1087) :=
  (RouteL.next (s:=(st 1095)) (q:=(st 1094)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1093)) (q:=(st 1092)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1091)) (q:=(st 1090)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1089)) (q:=(st 1087)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1087))))))

private theorem dec4 : DecRows 4 (st 1107) (st 270) (st 1087) := by
  exact ⟨(st 1099),(st 1088),(st 1098),(st 1097),(st 292),(st 1096),by decide,by decide,by decide,by decide,route17,route1,route18,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route19 : RouteR 0 11 (st 1087) (st 1065) :=
  (RouteR.next (s:=(st 1086)) (q:=(st 1085)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1084)) (q:=(st 1083)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1082)) (q:=(st 1081)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1080)) (q:=(st 1079)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1078)) (q:=(st 1077)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1076)) (q:=(st 1075)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1074)) (q:=(st 1073)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1072)) (q:=(st 1071)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1070)) (q:=(st 1069)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1068)) (q:=(st 1067)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1066)) (q:=(st 1065)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 1065)))))))))))))

private theorem route20 : RouteL 11 0 (st 1062) (st 1040) :=
  (RouteL.next (s:=(st 1061)) (q:=(st 1060)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1059)) (q:=(st 1058)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1057)) (q:=(st 1056)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1055)) (q:=(st 1054)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1053)) (q:=(st 1052)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1051)) (q:=(st 1050)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1049)) (q:=(st 1048)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1047)) (q:=(st 1046)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1045)) (q:=(st 1044)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1043)) (q:=(st 1042)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1041)) (q:=(st 1040)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1040)))))))))))))

private theorem inc4 : IncRows 11 (st 1087) (st 1040) := by
  exact ⟨(st 1065),(st 1064),(st 1063),(st 1062),by decide,by decide,by decide,route19,route20,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route21 : RouteR 0 4 (st 1302) (st 1294) :=
  (RouteR.next (s:=(st 1301)) (q:=(st 1300)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1299)) (q:=(st 1298)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1297)) (q:=(st 1296)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1295)) (q:=(st 1294)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 1294))))))

private theorem route22 : RouteL 4 0 (st 1291) (st 1282) :=
  (RouteL.next (s:=(st 1290)) (q:=(st 1289)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1288)) (q:=(st 1287)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1286)) (q:=(st 1285)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1284)) (q:=(st 1282)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1282))))))

private theorem dec5 : DecRows 4 (st 1302) (st 270) (st 1282) := by
  exact ⟨(st 1294),(st 1283),(st 1293),(st 1292),(st 292),(st 1291),by decide,by decide,by decide,by decide,route21,route1,route22,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route23 : RouteR 0 11 (st 1282) (st 1260) :=
  (RouteR.next (s:=(st 1281)) (q:=(st 1280)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1279)) (q:=(st 1278)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1277)) (q:=(st 1276)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1275)) (q:=(st 1274)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1273)) (q:=(st 1272)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1271)) (q:=(st 1270)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1269)) (q:=(st 1268)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1267)) (q:=(st 1266)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1265)) (q:=(st 1264)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1263)) (q:=(st 1262)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1261)) (q:=(st 1260)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 1260)))))))))))))

private theorem route24 : RouteL 11 0 (st 1257) (st 1235) :=
  (RouteL.next (s:=(st 1256)) (q:=(st 1255)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1254)) (q:=(st 1253)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1252)) (q:=(st 1251)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1250)) (q:=(st 1249)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1248)) (q:=(st 1247)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1246)) (q:=(st 1245)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1244)) (q:=(st 1243)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1242)) (q:=(st 1241)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1240)) (q:=(st 1239)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1238)) (q:=(st 1237)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1236)) (q:=(st 1235)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1235)))))))))))))

private theorem inc5 : IncRows 11 (st 1282) (st 1235) := by
  exact ⟨(st 1260),(st 1259),(st 1258),(st 1257),by decide,by decide,by decide,route23,route24,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route25 : RouteR 0 4 (st 1404) (st 1396) :=
  (RouteR.next (s:=(st 1403)) (q:=(st 1402)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1401)) (q:=(st 1400)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1399)) (q:=(st 1398)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1397)) (q:=(st 1396)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 1396))))))

private theorem route26 : RouteL 4 0 (st 1393) (st 1384) :=
  (RouteL.next (s:=(st 1392)) (q:=(st 1391)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1390)) (q:=(st 1389)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1388)) (q:=(st 1387)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1386)) (q:=(st 1384)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1384))))))

private theorem dec6 : DecRows 4 (st 1404) (st 270) (st 1384) := by
  exact ⟨(st 1396),(st 1385),(st 1395),(st 1394),(st 292),(st 1393),by decide,by decide,by decide,by decide,route25,route1,route26,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route27 : RouteR 0 11 (st 1384) (st 1362) :=
  (RouteR.next (s:=(st 1383)) (q:=(st 1382)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1381)) (q:=(st 1380)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1379)) (q:=(st 1378)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1377)) (q:=(st 1376)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1375)) (q:=(st 1374)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1373)) (q:=(st 1372)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1371)) (q:=(st 1370)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1369)) (q:=(st 1368)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1367)) (q:=(st 1366)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1365)) (q:=(st 1364)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1363)) (q:=(st 1362)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 1362)))))))))))))

private theorem route28 : RouteL 11 0 (st 1359) (st 1337) :=
  (RouteL.next (s:=(st 1358)) (q:=(st 1357)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1356)) (q:=(st 1355)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1354)) (q:=(st 1353)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1352)) (q:=(st 1351)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1350)) (q:=(st 1349)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1348)) (q:=(st 1347)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1346)) (q:=(st 1345)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1344)) (q:=(st 1343)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1342)) (q:=(st 1341)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1340)) (q:=(st 1339)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1338)) (q:=(st 1337)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1337)))))))))))))

private theorem inc6 : IncRows 11 (st 1384) (st 1337) := by
  exact ⟨(st 1362),(st 1361),(st 1360),(st 1359),by decide,by decide,by decide,route27,route28,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route29 : RouteR 0 4 (st 1506) (st 1498) :=
  (RouteR.next (s:=(st 1505)) (q:=(st 1504)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1503)) (q:=(st 1502)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1501)) (q:=(st 1500)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1499)) (q:=(st 1498)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 1498))))))

private theorem route30 : RouteL 4 0 (st 1495) (st 1486) :=
  (RouteL.next (s:=(st 1494)) (q:=(st 1493)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1492)) (q:=(st 1491)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1490)) (q:=(st 1489)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1488)) (q:=(st 1486)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1486))))))

private theorem dec7 : DecRows 4 (st 1506) (st 270) (st 1486) := by
  exact ⟨(st 1498),(st 1487),(st 1497),(st 1496),(st 292),(st 1495),by decide,by decide,by decide,by decide,route29,route1,route30,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route31 : RouteR 0 11 (st 1486) (st 1464) :=
  (RouteR.next (s:=(st 1485)) (q:=(st 1484)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1483)) (q:=(st 1482)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1481)) (q:=(st 1480)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1479)) (q:=(st 1478)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1477)) (q:=(st 1476)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1475)) (q:=(st 1474)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1473)) (q:=(st 1472)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1471)) (q:=(st 1470)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1469)) (q:=(st 1468)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1467)) (q:=(st 1466)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1465)) (q:=(st 1464)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 1464)))))))))))))

private theorem route32 : RouteL 11 0 (st 1461) (st 1439) :=
  (RouteL.next (s:=(st 1460)) (q:=(st 1459)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1458)) (q:=(st 1457)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1456)) (q:=(st 1455)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1454)) (q:=(st 1453)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1452)) (q:=(st 1451)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1450)) (q:=(st 1449)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1448)) (q:=(st 1447)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1446)) (q:=(st 1445)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1444)) (q:=(st 1443)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1442)) (q:=(st 1441)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1440)) (q:=(st 1439)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1439)))))))))))))

private theorem inc7 : IncRows 11 (st 1486) (st 1439) := by
  exact ⟨(st 1464),(st 1463),(st 1462),(st 1461),by decide,by decide,by decide,route31,route32,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route33 : RouteR 0 4 (st 2629) (st 2621) :=
  (RouteR.next (s:=(st 2628)) (q:=(st 2627)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2626)) (q:=(st 2625)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2624)) (q:=(st 2623)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2622)) (q:=(st 2621)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 2621))))))

private theorem route34 : RouteL 4 0 (st 2618) (st 2609) :=
  (RouteL.next (s:=(st 2617)) (q:=(st 2616)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2615)) (q:=(st 2614)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2613)) (q:=(st 2612)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2611)) (q:=(st 2609)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 2609))))))

private theorem dec8 : DecRows 4 (st 2629) (st 270) (st 2609) := by
  exact ⟨(st 2621),(st 2610),(st 2620),(st 2619),(st 292),(st 2618),by decide,by decide,by decide,by decide,route33,route1,route34,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route35 : RouteR 0 11 (st 2609) (st 2587) :=
  (RouteR.next (s:=(st 2608)) (q:=(st 2607)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2606)) (q:=(st 2605)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2604)) (q:=(st 2603)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2602)) (q:=(st 2601)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2600)) (q:=(st 2599)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2598)) (q:=(st 2597)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2596)) (q:=(st 2595)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2594)) (q:=(st 2593)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2592)) (q:=(st 2591)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2590)) (q:=(st 2589)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2588)) (q:=(st 2587)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 2587)))))))))))))

private theorem route36 : RouteL 11 0 (st 2584) (st 2562) :=
  (RouteL.next (s:=(st 2583)) (q:=(st 2582)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2581)) (q:=(st 2580)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2579)) (q:=(st 2578)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2577)) (q:=(st 2576)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2575)) (q:=(st 2574)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2573)) (q:=(st 2572)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2571)) (q:=(st 2570)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2569)) (q:=(st 2568)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2567)) (q:=(st 2566)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2565)) (q:=(st 2564)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2563)) (q:=(st 2562)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 2562)))))))))))))

private theorem inc8 : IncRows 11 (st 2609) (st 2562) := by
  exact ⟨(st 2587),(st 2586),(st 2585),(st 2584),by decide,by decide,by decide,route35,route36,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route37 : RouteR 0 4 (st 3467) (st 3459) :=
  (RouteR.next (s:=(st 3466)) (q:=(st 3465)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3464)) (q:=(st 3463)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3462)) (q:=(st 3461)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3460)) (q:=(st 3459)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 3459))))))

private theorem route38 : RouteL 4 0 (st 2348) (st 3307) :=
  (RouteL.next (s:=(st 2347)) (q:=(st 2346)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2345)) (q:=(st 2344)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2343)) (q:=(st 2342)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2341)) (q:=(st 3307)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3307))))))

private theorem route39 : RouteL 4 0 (st 3456) (st 3447) :=
  (RouteL.next (s:=(st 3455)) (q:=(st 3454)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3453)) (q:=(st 3452)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3451)) (q:=(st 3450)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3449)) (q:=(st 3447)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3447))))))

private theorem dec9 : DecRows 4 (st 3467) (st 3307) (st 3447) := by
  exact ⟨(st 3459),(st 3448),(st 3458),(st 3457),(st 2348),(st 3456),by decide,by decide,by decide,by decide,route37,route38,route39,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route40 : RouteR 0 11 (st 3447) (st 3425) :=
  (RouteR.next (s:=(st 3446)) (q:=(st 3445)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3444)) (q:=(st 3443)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3442)) (q:=(st 3441)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3440)) (q:=(st 3439)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3438)) (q:=(st 3437)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3436)) (q:=(st 3435)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3434)) (q:=(st 3433)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3432)) (q:=(st 3431)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3430)) (q:=(st 3429)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3428)) (q:=(st 3427)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3426)) (q:=(st 3425)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3425)))))))))))))

private theorem route41 : RouteL 11 0 (st 3418) (st 3396) :=
  (RouteL.next (s:=(st 3417)) (q:=(st 3416)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3415)) (q:=(st 3414)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3413)) (q:=(st 3412)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3411)) (q:=(st 3410)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3409)) (q:=(st 3408)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3407)) (q:=(st 3406)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3405)) (q:=(st 3404)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3403)) (q:=(st 3402)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3401)) (q:=(st 3400)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3399)) (q:=(st 3398)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3397)) (q:=(st 3396)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3396)))))))))))))

private theorem inc9 : IncRows 11 (st 3447) (st 3396) := by
  exact ⟨(st 3425),(st 3424),(st 3419),(st 3418),by decide,by decide,by decide,route40,route41,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route42 : RouteR 0 4 (st 3569) (st 3561) :=
  (RouteR.next (s:=(st 3568)) (q:=(st 3567)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3566)) (q:=(st 3565)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3564)) (q:=(st 3563)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3562)) (q:=(st 3561)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 3561))))))

private theorem route43 : RouteL 4 0 (st 3558) (st 3549) :=
  (RouteL.next (s:=(st 3557)) (q:=(st 3556)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3555)) (q:=(st 3554)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3553)) (q:=(st 3552)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3551)) (q:=(st 3549)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3549))))))

private theorem dec10 : DecRows 4 (st 3569) (st 3307) (st 3549) := by
  exact ⟨(st 3561),(st 3550),(st 3560),(st 3559),(st 2348),(st 3558),by decide,by decide,by decide,by decide,route42,route38,route43,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route44 : RouteR 0 11 (st 3549) (st 3527) :=
  (RouteR.next (s:=(st 3548)) (q:=(st 3547)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3546)) (q:=(st 3545)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3544)) (q:=(st 3543)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3542)) (q:=(st 3541)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3540)) (q:=(st 3539)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3538)) (q:=(st 3537)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3536)) (q:=(st 3535)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3534)) (q:=(st 3533)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3532)) (q:=(st 3531)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3530)) (q:=(st 3529)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3528)) (q:=(st 3527)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3527)))))))))))))

private theorem route45 : RouteL 11 0 (st 3524) (st 3502) :=
  (RouteL.next (s:=(st 3523)) (q:=(st 3522)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3521)) (q:=(st 3520)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3519)) (q:=(st 3518)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3517)) (q:=(st 3516)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3515)) (q:=(st 3514)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3513)) (q:=(st 3512)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3511)) (q:=(st 3510)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3509)) (q:=(st 3508)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3507)) (q:=(st 3506)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3505)) (q:=(st 3504)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3503)) (q:=(st 3502)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3502)))))))))))))

private theorem inc10 : IncRows 11 (st 3549) (st 3502) := by
  exact ⟨(st 3527),(st 3526),(st 3525),(st 3524),by decide,by decide,by decide,route44,route45,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route46 : RouteR 0 4 (st 3671) (st 3663) :=
  (RouteR.next (s:=(st 3670)) (q:=(st 3669)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3668)) (q:=(st 3667)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3666)) (q:=(st 3665)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3664)) (q:=(st 3663)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 3663))))))

private theorem route47 : RouteL 4 0 (st 3660) (st 3651) :=
  (RouteL.next (s:=(st 3659)) (q:=(st 3658)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3657)) (q:=(st 3656)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3655)) (q:=(st 3654)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3653)) (q:=(st 3651)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3651))))))

private theorem dec11 : DecRows 4 (st 3671) (st 3307) (st 3651) := by
  exact ⟨(st 3663),(st 3652),(st 3662),(st 3661),(st 2348),(st 3660),by decide,by decide,by decide,by decide,route46,route38,route47,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route48 : RouteR 0 11 (st 3651) (st 3629) :=
  (RouteR.next (s:=(st 3650)) (q:=(st 3649)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3648)) (q:=(st 3647)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3646)) (q:=(st 3645)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3644)) (q:=(st 3643)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3642)) (q:=(st 3641)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3640)) (q:=(st 3639)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3638)) (q:=(st 3637)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3636)) (q:=(st 3635)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3634)) (q:=(st 3633)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3632)) (q:=(st 3631)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3630)) (q:=(st 3629)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3629)))))))))))))

private theorem route49 : RouteL 11 0 (st 3626) (st 3604) :=
  (RouteL.next (s:=(st 3625)) (q:=(st 3624)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3623)) (q:=(st 3622)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3621)) (q:=(st 3620)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3619)) (q:=(st 3618)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3617)) (q:=(st 3616)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3615)) (q:=(st 3614)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3613)) (q:=(st 3612)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3611)) (q:=(st 3610)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3609)) (q:=(st 3608)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3607)) (q:=(st 3606)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3605)) (q:=(st 3604)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3604)))))))))))))

private theorem inc11 : IncRows 11 (st 3651) (st 3604) := by
  exact ⟨(st 3629),(st 3628),(st 3627),(st 3626),by decide,by decide,by decide,route48,route49,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route50 : RouteR 0 4 (st 3773) (st 3765) :=
  (RouteR.next (s:=(st 3772)) (q:=(st 3771)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3770)) (q:=(st 3769)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3768)) (q:=(st 3767)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3766)) (q:=(st 3765)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 3765))))))

private theorem route51 : RouteL 4 0 (st 3762) (st 3753) :=
  (RouteL.next (s:=(st 3761)) (q:=(st 3760)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3759)) (q:=(st 3758)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3757)) (q:=(st 3756)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3755)) (q:=(st 3753)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3753))))))

private theorem dec12 : DecRows 4 (st 3773) (st 3307) (st 3753) := by
  exact ⟨(st 3765),(st 3754),(st 3764),(st 3763),(st 2348),(st 3762),by decide,by decide,by decide,by decide,route50,route38,route51,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route52 : RouteR 0 11 (st 3753) (st 3731) :=
  (RouteR.next (s:=(st 3752)) (q:=(st 3751)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3750)) (q:=(st 3749)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3748)) (q:=(st 3747)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3746)) (q:=(st 3745)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3744)) (q:=(st 3743)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3742)) (q:=(st 3741)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3740)) (q:=(st 3739)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3738)) (q:=(st 3737)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3736)) (q:=(st 3735)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3734)) (q:=(st 3733)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3732)) (q:=(st 3731)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3731)))))))))))))

private theorem route53 : RouteL 11 0 (st 3728) (st 3706) :=
  (RouteL.next (s:=(st 3727)) (q:=(st 3726)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3725)) (q:=(st 3724)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3723)) (q:=(st 3722)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3721)) (q:=(st 3720)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3719)) (q:=(st 3718)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3717)) (q:=(st 3716)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3715)) (q:=(st 3714)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3713)) (q:=(st 3712)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3711)) (q:=(st 3710)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3709)) (q:=(st 3708)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3707)) (q:=(st 3706)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3706)))))))))))))

private theorem inc12 : IncRows 11 (st 3753) (st 3706) := by
  exact ⟨(st 3731),(st 3730),(st 3729),(st 3728),by decide,by decide,by decide,route52,route53,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route54 : RouteR 0 4 (st 3875) (st 3867) :=
  (RouteR.next (s:=(st 3874)) (q:=(st 3873)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3872)) (q:=(st 3871)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3870)) (q:=(st 3869)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3868)) (q:=(st 3867)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 3867))))))

private theorem route55 : RouteL 4 0 (st 3864) (st 3855) :=
  (RouteL.next (s:=(st 3863)) (q:=(st 3862)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3861)) (q:=(st 3860)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3859)) (q:=(st 3858)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3857)) (q:=(st 3855)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3855))))))

private theorem dec13 : DecRows 4 (st 3875) (st 3307) (st 3855) := by
  exact ⟨(st 3867),(st 3856),(st 3866),(st 3865),(st 2348),(st 3864),by decide,by decide,by decide,by decide,route54,route38,route55,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route56 : RouteR 0 11 (st 3855) (st 3833) :=
  (RouteR.next (s:=(st 3854)) (q:=(st 3853)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3852)) (q:=(st 3851)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3850)) (q:=(st 3849)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3848)) (q:=(st 3847)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3846)) (q:=(st 3845)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3844)) (q:=(st 3843)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3842)) (q:=(st 3841)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3840)) (q:=(st 3839)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3838)) (q:=(st 3837)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3836)) (q:=(st 3835)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3834)) (q:=(st 3833)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3833)))))))))))))

private theorem route57 : RouteL 11 0 (st 3830) (st 3808) :=
  (RouteL.next (s:=(st 3829)) (q:=(st 3828)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3827)) (q:=(st 3826)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3825)) (q:=(st 3824)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3823)) (q:=(st 3822)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3821)) (q:=(st 3820)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3819)) (q:=(st 3818)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3817)) (q:=(st 3816)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3815)) (q:=(st 3814)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3813)) (q:=(st 3812)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3811)) (q:=(st 3810)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3809)) (q:=(st 3808)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3808)))))))))))))

private theorem inc13 : IncRows 11 (st 3855) (st 3808) := by
  exact ⟨(st 3833),(st 3832),(st 3831),(st 3830),by decide,by decide,by decide,route56,route57,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route58 : RouteR 0 4 (st 3954) (st 3946) :=
  (RouteR.next (s:=(st 3953)) (q:=(st 3952)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3951)) (q:=(st 3950)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3949)) (q:=(st 3948)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3947)) (q:=(st 3946)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 3946))))))

private theorem route59 : RouteL 4 0 (st 3943) (st 3934) :=
  (RouteL.next (s:=(st 3942)) (q:=(st 3941)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3940)) (q:=(st 3939)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3938)) (q:=(st 3937)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3936)) (q:=(st 3934)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3934))))))

private theorem dec14 : DecRows 4 (st 3954) (st 3307) (st 3934) := by
  exact ⟨(st 3946),(st 3935),(st 3945),(st 3944),(st 2348),(st 3943),by decide,by decide,by decide,by decide,route58,route38,route59,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route60 : RouteR 0 11 (st 3934) (st 3912) :=
  (RouteR.next (s:=(st 3933)) (q:=(st 3932)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3931)) (q:=(st 3930)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3929)) (q:=(st 3928)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3927)) (q:=(st 3926)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3925)) (q:=(st 3924)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3923)) (q:=(st 3922)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3921)) (q:=(st 3920)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3919)) (q:=(st 3918)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3917)) (q:=(st 3916)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3915)) (q:=(st 3914)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3913)) (q:=(st 3912)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3912)))))))))))))

private theorem route61 : RouteL 11 0 (st 3909) (st 3887) :=
  (RouteL.next (s:=(st 3908)) (q:=(st 3907)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3906)) (q:=(st 3905)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3904)) (q:=(st 3903)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3902)) (q:=(st 3901)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3900)) (q:=(st 3899)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3898)) (q:=(st 3897)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3896)) (q:=(st 3895)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3894)) (q:=(st 3893)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3892)) (q:=(st 3891)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3890)) (q:=(st 3889)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3888)) (q:=(st 3887)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3887)))))))))))))

private theorem inc14 : IncRows 11 (st 3934) (st 3887) := by
  exact ⟨(st 3912),(st 3911),(st 3910),(st 3909),by decide,by decide,by decide,route60,route61,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route62 : RouteR 0 4 (st 4033) (st 4025) :=
  (RouteR.next (s:=(st 4032)) (q:=(st 4031)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4030)) (q:=(st 4029)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4028)) (q:=(st 4027)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4026)) (q:=(st 4025)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 4025))))))

private theorem route63 : RouteL 4 0 (st 4022) (st 4013) :=
  (RouteL.next (s:=(st 4021)) (q:=(st 4020)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4019)) (q:=(st 4018)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4017)) (q:=(st 4016)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4015)) (q:=(st 4013)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 4013))))))

private theorem dec15 : DecRows 4 (st 4033) (st 3307) (st 4013) := by
  exact ⟨(st 4025),(st 4014),(st 4024),(st 4023),(st 2348),(st 4022),by decide,by decide,by decide,by decide,route62,route38,route63,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route64 : RouteR 0 11 (st 4013) (st 3991) :=
  (RouteR.next (s:=(st 4012)) (q:=(st 4011)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4010)) (q:=(st 4009)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4008)) (q:=(st 4007)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4006)) (q:=(st 4005)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4004)) (q:=(st 4003)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4002)) (q:=(st 4001)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4000)) (q:=(st 3999)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3998)) (q:=(st 3997)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3996)) (q:=(st 3995)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3994)) (q:=(st 3993)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3992)) (q:=(st 3991)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3991)))))))))))))

private theorem route65 : RouteL 11 0 (st 3988) (st 3966) :=
  (RouteL.next (s:=(st 3987)) (q:=(st 3986)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3985)) (q:=(st 3984)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3983)) (q:=(st 3982)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3981)) (q:=(st 3980)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3979)) (q:=(st 3978)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3977)) (q:=(st 3976)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3975)) (q:=(st 3974)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3973)) (q:=(st 3972)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3971)) (q:=(st 3970)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3969)) (q:=(st 3968)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3967)) (q:=(st 3966)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3966)))))))))))))

private theorem inc15 : IncRows 11 (st 4013) (st 3966) := by
  exact ⟨(st 3991),(st 3990),(st 3989),(st 3988),by decide,by decide,by decide,route64,route65,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route66 : RouteR 0 4 (st 4132) (st 4124) :=
  (RouteR.next (s:=(st 4131)) (q:=(st 4130)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4129)) (q:=(st 4128)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4127)) (q:=(st 4126)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4125)) (q:=(st 4124)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 4124))))))

private theorem route67 : RouteL 4 0 (st 4121) (st 4112) :=
  (RouteL.next (s:=(st 4120)) (q:=(st 4119)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4118)) (q:=(st 4117)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4116)) (q:=(st 4115)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4114)) (q:=(st 4112)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 4112))))))

private theorem dec16 : DecRows 4 (st 4132) (st 3307) (st 4112) := by
  exact ⟨(st 4124),(st 4113),(st 4123),(st 4122),(st 2348),(st 4121),by decide,by decide,by decide,by decide,route66,route38,route67,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route68 : RouteR 0 11 (st 4112) (st 4090) :=
  (RouteR.next (s:=(st 4111)) (q:=(st 4110)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4109)) (q:=(st 4108)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4107)) (q:=(st 4106)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4105)) (q:=(st 4104)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4103)) (q:=(st 4102)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4101)) (q:=(st 4100)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4099)) (q:=(st 4098)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4097)) (q:=(st 4096)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4095)) (q:=(st 4094)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4093)) (q:=(st 4092)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4091)) (q:=(st 4090)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 4090)))))))))))))

private theorem route69 : RouteL 11 0 (st 4087) (st 4065) :=
  (RouteL.next (s:=(st 4086)) (q:=(st 4085)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4084)) (q:=(st 4083)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4082)) (q:=(st 4081)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4080)) (q:=(st 4079)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4078)) (q:=(st 4077)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4076)) (q:=(st 4075)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4074)) (q:=(st 4073)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4072)) (q:=(st 4071)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4070)) (q:=(st 4069)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4068)) (q:=(st 4067)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4066)) (q:=(st 4065)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 4065)))))))))))))

private theorem inc16 : IncRows 11 (st 4112) (st 4065) := by
  exact ⟨(st 4090),(st 4089),(st 4088),(st 4087),by decide,by decide,by decide,route68,route69,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route70 : RouteR 0 4 (st 5016) (st 5008) :=
  (RouteR.next (s:=(st 5015)) (q:=(st 5014)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5013)) (q:=(st 5012)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5011)) (q:=(st 5010)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5009)) (q:=(st 5008)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 5008))))))

private theorem route71 : RouteL 4 0 (st 5005) (st 4996) :=
  (RouteL.next (s:=(st 5004)) (q:=(st 5003)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5002)) (q:=(st 5001)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5000)) (q:=(st 4999)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4998)) (q:=(st 4996)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 4996))))))

private theorem dec17 : DecRows 4 (st 5016) (st 3307) (st 4996) := by
  exact ⟨(st 5008),(st 4997),(st 5007),(st 5006),(st 2348),(st 5005),by decide,by decide,by decide,by decide,route70,route38,route71,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route72 : RouteR 0 11 (st 4996) (st 4974) :=
  (RouteR.next (s:=(st 4995)) (q:=(st 4994)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4993)) (q:=(st 4992)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4991)) (q:=(st 4990)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4989)) (q:=(st 4988)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4987)) (q:=(st 4986)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4985)) (q:=(st 4984)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4983)) (q:=(st 4982)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4981)) (q:=(st 4980)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4979)) (q:=(st 4978)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4977)) (q:=(st 4976)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4975)) (q:=(st 4974)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 4974)))))))))))))

private theorem route73 : RouteL 11 0 (st 4971) (st 4949) :=
  (RouteL.next (s:=(st 4970)) (q:=(st 4969)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4968)) (q:=(st 4967)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4966)) (q:=(st 4965)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4964)) (q:=(st 4963)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4962)) (q:=(st 4961)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4960)) (q:=(st 4959)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4958)) (q:=(st 4957)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4956)) (q:=(st 4955)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4954)) (q:=(st 4953)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4952)) (q:=(st 4951)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4950)) (q:=(st 4949)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 4949)))))))))))))

private theorem inc17 : IncRows 11 (st 4996) (st 4949) := by
  exact ⟨(st 4974),(st 4973),(st 4972),(st 4971),by decide,by decide,by decide,route72,route73,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route74 : RouteR 0 4 (st 5811) (st 5803) :=
  (RouteR.next (s:=(st 5810)) (q:=(st 5809)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5808)) (q:=(st 5807)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5806)) (q:=(st 5805)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5804)) (q:=(st 5803)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 5803))))))

private theorem route75 : RouteL 4 0 (st 2409) (st 5685) :=
  (RouteL.next (s:=(st 2408)) (q:=(st 2407)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2406)) (q:=(st 2405)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2404)) (q:=(st 2403)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2402)) (q:=(st 5685)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5685))))))

private theorem route76 : RouteL 4 0 (st 5800) (st 5791) :=
  (RouteL.next (s:=(st 5799)) (q:=(st 5798)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5797)) (q:=(st 5796)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5795)) (q:=(st 5794)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5793)) (q:=(st 5791)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5791))))))

private theorem dec18 : DecRows 4 (st 5811) (st 5685) (st 5791) := by
  exact ⟨(st 5803),(st 5792),(st 5802),(st 5801),(st 2409),(st 5800),by decide,by decide,by decide,by decide,route74,route75,route76,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route77 : RouteR 0 11 (st 5791) (st 5769) :=
  (RouteR.next (s:=(st 5790)) (q:=(st 5789)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5788)) (q:=(st 5787)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5786)) (q:=(st 5785)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5784)) (q:=(st 5783)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5782)) (q:=(st 5781)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5780)) (q:=(st 5779)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5778)) (q:=(st 5777)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5776)) (q:=(st 5775)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5774)) (q:=(st 5773)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5772)) (q:=(st 5771)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5770)) (q:=(st 5769)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 5769)))))))))))))

private theorem route78 : RouteL 11 0 (st 5762) (st 5880) :=
  (RouteL.next (s:=(st 5761)) (q:=(st 5760)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5759)) (q:=(st 5758)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5757)) (q:=(st 5756)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5755)) (q:=(st 5754)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5753)) (q:=(st 5752)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5751)) (q:=(st 5750)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5749)) (q:=(st 5748)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5747)) (q:=(st 5746)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5745)) (q:=(st 5744)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5743)) (q:=(st 5742)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5741)) (q:=(st 5880)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5880)))))))))))))

private theorem inc18 : IncRows 11 (st 5791) (st 5880) := by
  exact ⟨(st 5769),(st 5768),(st 5763),(st 5762),by decide,by decide,by decide,route77,route78,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route79 : RouteR 0 4 (st 5879) (st 5871) :=
  (RouteR.next (s:=(st 5878)) (q:=(st 5877)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5876)) (q:=(st 5875)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5874)) (q:=(st 5873)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5872)) (q:=(st 5871)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 5871))))))

private theorem route80 : RouteL 4 0 (st 5868) (st 5859) :=
  (RouteL.next (s:=(st 5867)) (q:=(st 5866)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5865)) (q:=(st 5864)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5863)) (q:=(st 5862)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5861)) (q:=(st 5859)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5859))))))

private theorem dec19 : DecRows 4 (st 5879) (st 5685) (st 5859) := by
  exact ⟨(st 5871),(st 5860),(st 5870),(st 5869),(st 2409),(st 5868),by decide,by decide,by decide,by decide,route79,route75,route80,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route81 : RouteR 0 11 (st 5859) (st 5837) :=
  (RouteR.next (s:=(st 5858)) (q:=(st 5857)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5856)) (q:=(st 5855)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5854)) (q:=(st 5853)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5852)) (q:=(st 5851)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5850)) (q:=(st 5849)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5848)) (q:=(st 5847)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5846)) (q:=(st 5845)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5844)) (q:=(st 5843)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5842)) (q:=(st 5841)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5840)) (q:=(st 5839)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5838)) (q:=(st 5837)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 5837)))))))))))))

private theorem route82 : RouteL 11 0 (st 5834) (st 6016) :=
  (RouteL.next (s:=(st 5833)) (q:=(st 5832)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5831)) (q:=(st 5830)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5829)) (q:=(st 5828)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5827)) (q:=(st 5826)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5825)) (q:=(st 5824)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5823)) (q:=(st 5822)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5821)) (q:=(st 5820)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5819)) (q:=(st 5818)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5817)) (q:=(st 5816)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5815)) (q:=(st 5814)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5813)) (q:=(st 6016)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6016)))))))))))))

private theorem inc19 : IncRows 11 (st 5859) (st 6016) := by
  exact ⟨(st 5837),(st 5836),(st 5835),(st 5834),by decide,by decide,by decide,route81,route82,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route83 : RouteR 0 4 (st 5947) (st 5939) :=
  (RouteR.next (s:=(st 5946)) (q:=(st 5945)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5944)) (q:=(st 5943)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5942)) (q:=(st 5941)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5940)) (q:=(st 5939)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 5939))))))

private theorem route84 : RouteL 4 0 (st 5936) (st 5927) :=
  (RouteL.next (s:=(st 5935)) (q:=(st 5934)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5933)) (q:=(st 5932)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5931)) (q:=(st 5930)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5929)) (q:=(st 5927)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5927))))))

private theorem dec20 : DecRows 4 (st 5947) (st 5685) (st 5927) := by
  exact ⟨(st 5939),(st 5928),(st 5938),(st 5937),(st 2409),(st 5936),by decide,by decide,by decide,by decide,route83,route75,route84,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route85 : RouteR 0 11 (st 5927) (st 5905) :=
  (RouteR.next (s:=(st 5926)) (q:=(st 5925)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5924)) (q:=(st 5923)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5922)) (q:=(st 5921)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5920)) (q:=(st 5919)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5918)) (q:=(st 5917)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5916)) (q:=(st 5915)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5914)) (q:=(st 5913)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5912)) (q:=(st 5911)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5910)) (q:=(st 5909)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5908)) (q:=(st 5907)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5906)) (q:=(st 5905)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 5905)))))))))))))

private theorem route86 : RouteL 11 0 (st 5902) (st 6152) :=
  (RouteL.next (s:=(st 5901)) (q:=(st 5900)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5899)) (q:=(st 5898)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5897)) (q:=(st 5896)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5895)) (q:=(st 5894)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5893)) (q:=(st 5892)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5891)) (q:=(st 5890)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5889)) (q:=(st 5888)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5887)) (q:=(st 5886)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5885)) (q:=(st 5884)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5883)) (q:=(st 5882)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5881)) (q:=(st 6152)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6152)))))))))))))

private theorem inc20 : IncRows 11 (st 5927) (st 6152) := by
  exact ⟨(st 5905),(st 5904),(st 5903),(st 5902),by decide,by decide,by decide,route85,route86,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route87 : RouteR 0 4 (st 6015) (st 6007) :=
  (RouteR.next (s:=(st 6014)) (q:=(st 6013)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6012)) (q:=(st 6011)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6010)) (q:=(st 6009)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6008)) (q:=(st 6007)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 6007))))))

private theorem route88 : RouteL 4 0 (st 6004) (st 5995) :=
  (RouteL.next (s:=(st 6003)) (q:=(st 6002)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6001)) (q:=(st 6000)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5999)) (q:=(st 5998)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5997)) (q:=(st 5995)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5995))))))

private theorem dec21 : DecRows 4 (st 6015) (st 5685) (st 5995) := by
  exact ⟨(st 6007),(st 5996),(st 6006),(st 6005),(st 2409),(st 6004),by decide,by decide,by decide,by decide,route87,route75,route88,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route89 : RouteR 0 11 (st 5995) (st 5973) :=
  (RouteR.next (s:=(st 5994)) (q:=(st 5993)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5992)) (q:=(st 5991)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5990)) (q:=(st 5989)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5988)) (q:=(st 5987)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5986)) (q:=(st 5985)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5984)) (q:=(st 5983)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5982)) (q:=(st 5981)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5980)) (q:=(st 5979)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5978)) (q:=(st 5977)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5976)) (q:=(st 5975)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5974)) (q:=(st 5973)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 5973)))))))))))))

private theorem route90 : RouteL 11 0 (st 5970) (st 6943) :=
  (RouteL.next (s:=(st 5969)) (q:=(st 5968)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5967)) (q:=(st 5966)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5965)) (q:=(st 5964)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5963)) (q:=(st 5962)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5961)) (q:=(st 5960)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5959)) (q:=(st 5958)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5957)) (q:=(st 5956)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5955)) (q:=(st 5954)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5953)) (q:=(st 5952)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5951)) (q:=(st 5950)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5949)) (q:=(st 6943)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6943)))))))))))))

private theorem inc21 : IncRows 11 (st 5995) (st 6943) := by
  exact ⟨(st 5973),(st 5972),(st 5971),(st 5970),by decide,by decide,by decide,route89,route90,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route91 : RouteR 0 4 (st 6083) (st 6075) :=
  (RouteR.next (s:=(st 6082)) (q:=(st 6081)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6080)) (q:=(st 6079)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6078)) (q:=(st 6077)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6076)) (q:=(st 6075)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 6075))))))

private theorem route92 : RouteL 4 0 (st 6072) (st 6063) :=
  (RouteL.next (s:=(st 6071)) (q:=(st 6070)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6069)) (q:=(st 6068)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6067)) (q:=(st 6066)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6065)) (q:=(st 6063)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6063))))))

private theorem dec22 : DecRows 4 (st 6083) (st 5685) (st 6063) := by
  exact ⟨(st 6075),(st 6064),(st 6074),(st 6073),(st 2409),(st 6072),by decide,by decide,by decide,by decide,route91,route75,route92,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route93 : RouteR 0 11 (st 6063) (st 6041) :=
  (RouteR.next (s:=(st 6062)) (q:=(st 6061)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6060)) (q:=(st 6059)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6058)) (q:=(st 6057)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6056)) (q:=(st 6055)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6054)) (q:=(st 6053)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6052)) (q:=(st 6051)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6050)) (q:=(st 6049)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6048)) (q:=(st 6047)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6046)) (q:=(st 6045)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6044)) (q:=(st 6043)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6042)) (q:=(st 6041)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 6041)))))))))))))

private theorem route94 : RouteL 11 0 (st 6038) (st 913) :=
  (RouteL.next (s:=(st 6037)) (q:=(st 6036)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6035)) (q:=(st 6034)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6033)) (q:=(st 6032)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6031)) (q:=(st 6030)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6029)) (q:=(st 6028)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6027)) (q:=(st 6026)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6025)) (q:=(st 6024)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6023)) (q:=(st 6022)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6021)) (q:=(st 6020)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6019)) (q:=(st 6018)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6017)) (q:=(st 913)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 913)))))))))))))

private theorem inc22 : IncRows 11 (st 6063) (st 913) := by
  exact ⟨(st 6041),(st 6040),(st 6039),(st 6038),by decide,by decide,by decide,route93,route94,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route95 : RouteR 0 4 (st 6151) (st 6143) :=
  (RouteR.next (s:=(st 6150)) (q:=(st 6149)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6148)) (q:=(st 6147)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6146)) (q:=(st 6145)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6144)) (q:=(st 6143)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 6143))))))

private theorem route96 : RouteL 4 0 (st 6140) (st 6131) :=
  (RouteL.next (s:=(st 6139)) (q:=(st 6138)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6137)) (q:=(st 6136)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6135)) (q:=(st 6134)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6133)) (q:=(st 6131)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6131))))))

private theorem dec23 : DecRows 4 (st 6151) (st 5685) (st 6131) := by
  exact ⟨(st 6143),(st 6132),(st 6142),(st 6141),(st 2409),(st 6140),by decide,by decide,by decide,by decide,route95,route75,route96,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route97 : RouteR 0 11 (st 6131) (st 6109) :=
  (RouteR.next (s:=(st 6130)) (q:=(st 6129)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6128)) (q:=(st 6127)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6126)) (q:=(st 6125)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6124)) (q:=(st 6123)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6122)) (q:=(st 6121)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6120)) (q:=(st 6119)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6118)) (q:=(st 6117)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6116)) (q:=(st 6115)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6114)) (q:=(st 6113)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6112)) (q:=(st 6111)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6110)) (q:=(st 6109)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 6109)))))))))))))

private theorem route98 : RouteL 11 0 (st 6106) (st 1201) :=
  (RouteL.next (s:=(st 6105)) (q:=(st 6104)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6103)) (q:=(st 6102)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6101)) (q:=(st 6100)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6099)) (q:=(st 6098)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6097)) (q:=(st 6096)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6095)) (q:=(st 6094)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6093)) (q:=(st 6092)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6091)) (q:=(st 6090)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6089)) (q:=(st 6088)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6087)) (q:=(st 6086)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6085)) (q:=(st 1201)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1201)))))))))))))

private theorem inc23 : IncRows 11 (st 6131) (st 1201) := by
  exact ⟨(st 6109),(st 6108),(st 6107),(st 6106),by decide,by decide,by decide,route97,route98,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route99 : RouteR 0 4 (st 6197) (st 6189) :=
  (RouteR.next (s:=(st 6196)) (q:=(st 6195)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6194)) (q:=(st 6193)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6192)) (q:=(st 6191)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6190)) (q:=(st 6189)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 6189))))))

private theorem route100 : RouteL 4 0 (st 6186) (st 6177) :=
  (RouteL.next (s:=(st 6185)) (q:=(st 6184)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6183)) (q:=(st 6182)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6181)) (q:=(st 6180)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6179)) (q:=(st 6177)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6177))))))

private theorem dec24 : DecRows 4 (st 6197) (st 5685) (st 6177) := by
  exact ⟨(st 6189),(st 6178),(st 6188),(st 6187),(st 2409),(st 6186),by decide,by decide,by decide,by decide,route99,route75,route100,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route101 : RouteR 0 11 (st 6177) (st 6155) :=
  (RouteR.next (s:=(st 6176)) (q:=(st 6175)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6174)) (q:=(st 6173)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6172)) (q:=(st 6171)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6170)) (q:=(st 6169)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6168)) (q:=(st 6167)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6166)) (q:=(st 6165)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6164)) (q:=(st 6163)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6162)) (q:=(st 6161)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6160)) (q:=(st 6159)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6158)) (q:=(st 6157)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6156)) (q:=(st 6155)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 6155)))))))))))))

private theorem route102 : RouteL 11 0 (st 5765) (st 5685) :=
  (RouteL.next (s:=(st 5764)) (q:=(st 2421)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2420)) (q:=(st 2419)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2418)) (q:=(st 2417)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2416)) (q:=(st 2415)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2414)) (q:=(st 2413)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2412)) (q:=(st 2411)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2410)) (q:=(st 2409)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2408)) (q:=(st 2407)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2406)) (q:=(st 2405)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2404)) (q:=(st 2403)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2402)) (q:=(st 5685)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5685)))))))))))))

private theorem inc24 : IncRows 11 (st 6177) (st 5685) := by
  exact ⟨(st 6155),(st 6154),(st 6153),(st 5765),by decide,by decide,by decide,route101,route102,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route103 : RouteR 0 4 (st 6265) (st 6257) :=
  (RouteR.next (s:=(st 6264)) (q:=(st 6263)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6262)) (q:=(st 6261)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6260)) (q:=(st 6259)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6258)) (q:=(st 6257)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 6257))))))

private theorem route104 : RouteL 4 0 (st 6254) (st 6245) :=
  (RouteL.next (s:=(st 6253)) (q:=(st 6252)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6251)) (q:=(st 6250)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6249)) (q:=(st 6248)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6247)) (q:=(st 6245)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6245))))))

private theorem dec25 : DecRows 4 (st 6265) (st 5685) (st 6245) := by
  exact ⟨(st 6257),(st 6246),(st 6256),(st 6255),(st 2409),(st 6254),by decide,by decide,by decide,by decide,route103,route75,route104,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route105 : RouteR 0 11 (st 6245) (st 6223) :=
  (RouteR.next (s:=(st 6244)) (q:=(st 6243)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6242)) (q:=(st 6241)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6240)) (q:=(st 6239)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6238)) (q:=(st 6237)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6236)) (q:=(st 6235)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6234)) (q:=(st 6233)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6232)) (q:=(st 6231)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6230)) (q:=(st 6229)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6228)) (q:=(st 6227)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6226)) (q:=(st 6225)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 6224)) (q:=(st 6223)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 6223)))))))))))))

private theorem route106 : RouteL 11 0 (st 6220) (st 6612) :=
  (RouteL.next (s:=(st 6219)) (q:=(st 6218)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6217)) (q:=(st 6216)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6215)) (q:=(st 6214)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6213)) (q:=(st 6212)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6211)) (q:=(st 6210)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6209)) (q:=(st 6208)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6207)) (q:=(st 6206)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6205)) (q:=(st 6204)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6203)) (q:=(st 6202)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6201)) (q:=(st 6200)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 6199)) (q:=(st 6612)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 6612)))))))))))))

private theorem inc25 : IncRows 11 (st 6245) (st 6612) := by
  exact ⟨(st 6223),(st 6222),(st 6221),(st 6220),by decide,by decide,by decide,route105,route106,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route107 : RouteR 0 4 (st 7083) (st 7075) :=
  (RouteR.next (s:=(st 7082)) (q:=(st 7081)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7080)) (q:=(st 7079)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7078)) (q:=(st 7077)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7076)) (q:=(st 7075)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 7075))))))

private theorem route108 : RouteL 4 0 (st 7072) (st 7063) :=
  (RouteL.next (s:=(st 7071)) (q:=(st 7070)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7069)) (q:=(st 7068)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7067)) (q:=(st 7066)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7065)) (q:=(st 7063)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 7063))))))

private theorem dec26 : DecRows 4 (st 7083) (st 5685) (st 7063) := by
  exact ⟨(st 7075),(st 7064),(st 7074),(st 7073),(st 2409),(st 7072),by decide,by decide,by decide,by decide,route107,route75,route108,rfl,rfl,
    (by intro b hb; cases b with | none => rfl | some b => cases b with | false => rfl | true => exact False.elim (hb rfl)),rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

private theorem route109 : RouteR 0 11 (st 7063) (st 7041) :=
  (RouteR.next (s:=(st 7062)) (q:=(st 7061)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7060)) (q:=(st 7059)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7058)) (q:=(st 7057)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7056)) (q:=(st 7055)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7054)) (q:=(st 7053)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7052)) (q:=(st 7051)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7050)) (q:=(st 7049)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7048)) (q:=(st 7047)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7046)) (q:=(st 7045)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7044)) (q:=(st 7043)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7042)) (q:=(st 7041)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 7041)))))))))))))

private theorem route110 : RouteL 11 0 (st 7038) (st 2462) :=
  (RouteL.next (s:=(st 7037)) (q:=(st 7036)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7035)) (q:=(st 7034)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7033)) (q:=(st 7032)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7031)) (q:=(st 7030)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7029)) (q:=(st 7028)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7027)) (q:=(st 7026)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7025)) (q:=(st 7024)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7023)) (q:=(st 7022)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7021)) (q:=(st 7020)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7019)) (q:=(st 7018)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 7017)) (q:=(st 2462)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 2462)))))))))))))

private theorem inc26 : IncRows 11 (st 7063) (st 2462) := by
  exact ⟨(st 7041),(st 7040),(st 7039),(st 7038),by decide,by decide,by decide,route109,route110,rfl,rfl,rfl,(by intro b; cases b <;> rfl),rfl⟩

end LiteralRows
private theorem Path.prefix {P t c d} (path : Path P t c d) {N B : Nat}
    (fit : P < tapeLength N B) : ∀ u,u < t →
    (SerializedBody.machine.run u (embed c (lt_of_le_of_lt path.bounds.1 fit))).state.val ≥ 4 := by
  induction path with
  | nil => intro u hu; omega
  | @cons t c d e edge rest ih =>
    intro u hu
    cases u with
    | zero => exact edge.nonterminal
    | succ u =>
      have one : Path P 1 c d := Path.cons edge (Path.nil _ edge.after)
      rw [show u+1=1+u by omega,SerializedBody.machine.run_add,one.execute fit]
      exact ih u (by omega)

private theorem Path.through {P t c d} (path : Path P t c d) {N B : Nat}
    (fit : P < tapeLength N B) (last : 4 ≤ d.state.val) : ∀ u,u ≤ t →
    (SerializedBody.machine.run u (embed c (lt_of_le_of_lt path.bounds.1 fit))).state.val ≥ 4 := by
  intro u hu
  by_cases eq : u=t
  · subst u; rw [path.execute fit]; exact last
  · exact path.prefix fit u (by omega)
-- Public finite control-address API only; these maps are NOT a new machine.
def getEntry (site : Fin 9) (mode : Fin 3) : Fin 7500 := st (#[450,552,654,756,1107,1302,1404,1506,2629,3467,3569,3671,3773,3875,3954,4033,4132,5016,5811,5879,5947,6015,6083,6151,6197,6265,7083][9*mode.val+site.val]!)
private def pin_getEntry : Fin 9 → Fin 3 → Fin 7500 := getEntry
#print axioms SerializedBodyRefinement.getEntry
#print axioms pin_getEntry
def getBody (site : Fin 9) (mode : Fin 3) : Fin 7500 := st (#[371,485,587,689,1040,1235,1337,1439,2562,3396,3502,3604,3706,3808,3887,3966,4065,4949,5880,6016,6152,6943,913,1201,5685,6612,2462][9*mode.val+site.val]!)
private def pin_getBody : Fin 9 → Fin 3 → Fin 7500 := getBody
#print axioms SerializedBodyRefinement.getBody
#print axioms pin_getBody
def getAbort (mode : Fin 3) : Fin 7500 := st (#[270,3307,5685][mode.val]!)
private def pin_getAbort : Fin 3 → Fin 7500 := getAbort
#print axioms SerializedBodyRefinement.getAbort
#print axioms pin_getAbort
private theorem get_codes (site : Fin 9) (mode : Fin 3) :
  ∃ c : Fin 7500, DecRows 4 (getEntry site mode) (getAbort mode) c ∧ IncRows 11 c (getBody site mode) := by
  fin_cases mode <;> fin_cases site
  · exact ⟨st 430,dec0,inc0⟩
  · exact ⟨st 532,dec1,inc1⟩
  · exact ⟨st 634,dec2,inc2⟩
  · exact ⟨st 736,dec3,inc3⟩
  · exact ⟨st 1087,dec4,inc4⟩
  · exact ⟨st 1282,dec5,inc5⟩
  · exact ⟨st 1384,dec6,inc6⟩
  · exact ⟨st 1486,dec7,inc7⟩
  · exact ⟨st 2609,dec8,inc8⟩
  · exact ⟨st 3447,dec9,inc9⟩
  · exact ⟨st 3549,dec10,inc10⟩
  · exact ⟨st 3651,dec11,inc11⟩
  · exact ⟨st 3753,dec12,inc12⟩
  · exact ⟨st 3855,dec13,inc13⟩
  · exact ⟨st 3934,dec14,inc14⟩
  · exact ⟨st 4013,dec15,inc15⟩
  · exact ⟨st 4112,dec16,inc16⟩
  · exact ⟨st 4996,dec17,inc17⟩
  · exact ⟨st 5791,dec18,inc18⟩
  · exact ⟨st 5859,dec19,inc19⟩
  · exact ⟨st 5927,dec20,inc20⟩
  · exact ⟨st 5995,dec21,inc21⟩
  · exact ⟨st 6063,dec22,inc22⟩
  · exact ⟨st 6131,dec23,inc23⟩
  · exact ⟨st 6177,dec24,inc24⟩
  · exact ⟨st 6245,dec25,inc25⟩
  · exact ⟨st 7063,dec26,inc26⟩
private theorem controls_safe (site : Fin 9) (mode : Fin 3) :
    4 ≤ (getAbort mode).val ∧ 4 ≤ (getBody site mode).val := by
  fin_cases mode <;> fin_cases site <;> decide
/-- Full physical counter phase of EVERY actual Get site; no source read is
hidden here. A zero remaining field reaches the actual live abort entry. -/
theorem counter_phase (site : Fin 9) (mode : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (r v u N B P : Nat) (hv : v+u ≤ r)
    (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (rem : ∀ i,D 4 < i → i < D 5 → T i=some (decide (i-D 4 ≤ v)))
    (used : ∀ i,D 11 < i → i < D 12 → T i=some (decide (i-D 11 ≤ u)))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let steps:=if v=0 then 2*(D 4-D 0+4)+3 else 2*(D 4-D 0+4)+2*(D 11-D 0+11)+2*v+2*u+8
    let last:=if v=0 then getAbort mode else getBody site mode
    let U:=if v=0 then T else fun i => if i=D 11+u+1 then some true else if i=D 4+v then some false else T i
    let initial : Config 7500 N B:=⟨getEntry site mode,⟨D 0,h0⟩,fun i=>T i.val⟩
    SerializedBody.machine.run steps initial=⟨last,⟨D 0,h0⟩,fun i=>U i.val⟩ ∧
      ∀ t,t ≤ steps → 4 ≤ (SerializedBody.machine.run t initial).state.val := by
  dsimp only
  let grid : Grid D T:=⟨rise,mono,blank,cells⟩
  obtain ⟨c,dec,inc⟩:=get_codes site mode
  have small : v ≤ r := by omega
  by_cases zero : v=0
  · subst v
    simp only [↓reduceIte]
    have path:=dec_zero grid (by decide) room len4 rem dec
    constructor
    · simpa only [embed] using path.execute fit
    · simpa only [embed] using path.through fit (controls_safe site mode).1
  · simp only [if_neg zero]
    have positive : 0 < v := by omega
    have old:=unary_true rem len4 small (i:=D 4+v) (by omega) le_rfl
    let U:=put T (D 4+v) (some false)
    have gu : Grid D U:=grid.change_some _ true false old
    have first:=dec_positive grid (by decide) room len4 rem positive small dec
    have used' : Unary D U 11 u := by
      intro i lo hi
      have order:=mono 5 11 (by decide) (by decide)
      have ne : i≠D 4+v := by omega
      simp only [U,put,if_neg ne]; exact used i lo hi
    have second:=inc_success gu (by decide) room len11 used' (by omega) inc
    have path:=first.append second
    have time : 2*(D 4-D 0+4)+2*v+4+(2*(D 11-D 0+11)+2*u+4)=
        2*(D 4-D 0+4)+2*(D 11-D 0+11)+2*v+2*u+8 := by omega
    rw [time] at path
    constructor
    · simpa only [embed,U,put] using path.execute fit
    · simpa only [embed] using path.through fit (controls_safe site mode).2
/-- Independently restated native Config proposition, with renamed variables. -/
theorem counter_phase_mirror (call : Fin 9) (carry : Fin 3) (d : Nat → Nat) (mem : Nat → Option Bool)
    (cap left count inputN budget extent : Nat) (bounded : left+count ≤ cap)
    (ascending : ∀ j,j < 12 → d j < d (j+1))
    (ordered : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b)
    (delimiters : ∀ j,j ≤ 12 → mem (d j)=none)
    (occupied : ∀ j i,j < 12 → d j < i → i < d (j+1) → ∃ b,mem i=some b)
    (remainingWidth : d 5=d 4+cap+1) (usedWidth : d 12=d 11+cap+1)
    (remaining : ∀ i,d 4 < i → i < d 5 → mem i=some (decide (i-d 4 ≤ left)))
    (consumed : ∀ i,d 11 < i → i < d 12 → mem i=some (decide (i-d 11 ≤ count)))
    (physicalRoom : d 12 ≤ extent) (fits : extent < tapeLength inputN budget)
    (headFits : d 0 < tapeLength inputN budget) :
    let ticks:=if left=0 then 2*(d 4-d 0+4)+3 else 2*(d 4-d 0+4)+2*(d 11-d 0+11)+2*left+2*count+8
    let q:=if left=0 then getAbort carry else getBody call carry
    let tape:=if left=0 then mem else fun i => if i=d 11+count+1 then some true else if i=d 4+left then some false else mem i
    let begin : Config 7500 inputN budget:=⟨getEntry call carry,⟨d 0,headFits⟩,fun i=>mem i.val⟩
    SerializedBody.machine.run ticks begin=⟨q,⟨d 0,headFits⟩,fun i=>tape i.val⟩ ∧
      ∀ j,j ≤ ticks → 4 ≤ (SerializedBody.machine.run j begin).state.val := by
  exact counter_phase call carry d mem cap left count inputN budget extent bounded ascending ordered delimiters occupied remainingWidth usedWidth remaining consumed physicalRoom fits headFits
#print axioms SerializedBodyRefinement.counter_phase
#print axioms SerializedBodyRefinement.counter_phase_mirror
end SerializedBodyRefinement
