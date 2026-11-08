import SerializedBodyRefinement.Surface
namespace SerializedBodyCompletion
open Pnp3.Complexity.Uniform.V1
-- Counted proof-side path engine, reused as fresh counted source for missing cleanup/DFS phases.
-- No private donor term/name extraction; every edge is the same immutable physical table.
-- One Edge is proved equal to one actual frozen SerializedBody.machine step.
private structure Node where
  state : Fin 7500
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {N B : Nat} (c : Node) (h : c.head < tapeLength N B) : Config 7500 N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (P : Nat) (c d : Node) : Prop where
  nonterminal : 4 ≤ c.state.val
  before : c.head ≤ P
  after : d.head ≤ P
  row : (SerializedBody.machine.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (SerializedBody.machine.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (SerializedBody.machine.step c.state (c.tape c.head)).2.1
private inductive Path (P : Nat) : Nat → Node → Node → Prop
  | nil (c) (h : c.head ≤ P) : Path P 0 c c
  | cons {t c d e} : Edge P c d → Path P t d e → Path P (t+1) c e
namespace Path
private theorem bounds {P t c d} (h : Path P t c d) : c.head ≤ P ∧ d.head ≤ P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {P t u c d e} (h : Path P t c d) (g : Path P u d e) :
    Path P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {N B P t c d} (h : Path P t c d) (hp : P < tapeLength N B) :
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
        have hr : c.head+1 < tapeLength N B := by omega
        simp only [moveHead,embed,hr,↓reduceDIte]
        exact hm
    · funext i
      dsimp only [UniformTM.stepConfig,embed]
      rw [e.tape]
      simp only [put,Fin.ext_iff]
  suffices aux : ∀ (hc : c.head < tapeLength N B) (hd : d.head < tapeLength N B),
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
private theorem hop {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (safe : 4 ≤ s.val)
    (row : SerializedBody.machine.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨safe,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
private theorem keep {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (safe : 4 ≤ s.val)
    (row : SerializedBody.machine.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hb ha safe row hm
  rwa [put_same] at one
private theorem sweepR {P : Nat} (s : Fin 7500) (T : Nat → Option Bool) (h r : Nat) (fit : h+r ≤ P) (safe : 4 ≤ s.val) (rows : ∀ i, h ≤ i → i < h+r → SerializedBody.machine.step s (T i)=(s,T i,.right)) :
    Path P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right (P := P) (by omega) (by omega) safe (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {P : Nat} (s : Fin 7500) (T : Nat → Option Bool) (low r : Nat) (fit : low+r ≤ P) (safe : 4 ≤ s.val) (rows : ∀ i, low < i → i ≤ low+r → SerializedBody.machine.step s (T i)=(s,T i,.left)) :
    Path P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega) safe (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest

private theorem crossR {P : Nat} (e s q : Fin 7500) (T : Nat → Option Bool)
    (a w : Nat) (fit : a+w+1 ≤ P) (safeE : 4 ≤ e.val) (safeS : 4 ≤ s.val)
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
    (a w : Nat) (fit : a+w+1 ≤ P) (safeE : 4 ≤ e.val) (safeS : 4 ≤ s.val)
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
private def st (i : Nat) : Fin 7500 := ⟨i%7500,Nat.mod_lt _ (by decide)⟩
private theorem bounded_mono (D : Nat → Nat) (m : Nat)
    (rise : ∀ k, k < m → D k < D (k+1)) : ∀ a b, a ≤ b → b ≤ m → D a ≤ D b := by
  intro a b
  induction b generalizing a with
  | zero =>
    intro h _
    have eq : a=0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    intro h hm
    by_cases eq : a=b+1
    · subst a; exact le_rfl
    · exact le_trans (ih a (by omega) (by omega)) (Nat.le_of_lt (rise b (by omega)))
private def header (S L H j : Nat) : Nat := if j=0 then S else if j=1 then L else H
private theorem header_rise {S L H} (sl : S < L) (lh : L < H) :
    ∀ k, k < 2 → header S L H k < header S L H (k+1) := by
  intro k hk
  interval_cases k <;> simp only [header,↓reduceIte] <;> assumption
private theorem header_right {S L H P T e q} (sl : S < L) (lh : L < H)
    (fit : H ≤ P) (ts : T S=none) (tl : T L=none) (th : T H=none)
    (reg : ∀ i, S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i, L < i → i < H → ∃ b,T i=some b)
    (rows : RouteR 0 2 e q) : Path P (H-S+2) ⟨e,S,T⟩ ⟨q,H,T⟩ := by
  have r:=rows.execute (header S L H) T fit (by intro k _ hi; exact header_rise sl lh k hi)
    (by intro a b _ ab hi; exact bounded_mono _ 2 (header_rise sl lh) a b ab hi)
    (by intro k _ hi; interval_cases k <;> first | exact ts | exact tl | exact th)
    (by intro k i _ hi lo up; interval_cases k <;> first | exact reg i lo up | exact ass i lo up)
  exact r
private theorem header_left {S L H P T e q} (sl : S < L) (lh : L < H)
    (fit : H ≤ P) (ts : T S=none) (tl : T L=none) (th : T H=none)
    (reg : ∀ i, S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i, L < i → i < H → ∃ b,T i=some b)
    (rows : RouteL 2 0 e q) : Path P (H-S+2) ⟨e,H,T⟩ ⟨q,S,T⟩ := by
  have r:=rows.execute (header S L H) T fit (by intro k _ hi; exact header_rise sl lh k hi)
    (by intro a b _ ab hi; exact bounded_mono _ 2 (header_rise sl lh) a b ab hi)
    (by intro k _ hi; interval_cases k <;> first | exact ts | exact tl | exact th)
    (by intro k i _ hi lo up; interval_cases k <;> first | exact reg i lo up | exact ass i lo up)
  exact r
private def ToHRows (entry out : Fin 7500) : Prop :=
  ∃ fence gap mark : Fin 7500, 4 ≤ entry.val ∧ 4 ≤ fence.val ∧ 4 ≤ gap.val ∧ 4 ≤ mark.val ∧
    SerializedBody.machine.step entry none=(fence,none,.left) ∧
    SerializedBody.machine.step fence (some false)=(gap,some false,.left) ∧
    SerializedBody.machine.step gap none=(gap,none,.left) ∧
    SerializedBody.machine.step gap (some true)=(mark,some true,.left) ∧
    SerializedBody.machine.step mark (some true)=(mark,some true,.left) ∧
    SerializedBody.machine.step mark none=(out,none,.stay)
private theorem to_H {H Q F P T entry out} (positive : 0 < Q) (room : H+Q < F)
    (fit : F+1 ≤ P) (td : T (F+1)=none) (tf : T F=some false) (th : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none) (rows : ToHRows entry out) :
    Path P (F+2-H) ⟨entry,F+1,T⟩ ⟨out,H,T⟩ := by
  rcases rows with ⟨f,g,m,se,sf,sg,sm,re,rf,rg,rt,rm,rn⟩
  have one:=keep entry f (F+1) F T .left (P:=P) fit (by omega) se (by rw [td]; exact re) (by simp [dest])
  have two:=keep f g F (F-1) T .left (P:=P) (by omega) (by omega) sf (by rw [tf]; exact rf) rfl
  have gs:=sweepL g T (H+Q) (F-1-(H+Q)) (P:=P) (by omega) sg (by
    intro i lo hi; rw [gap i lo (by omega)]; exact rg)
  rw [show H+Q+(F-1-(H+Q))=F-1 by omega] at gs
  have take:=keep g m (H+Q) (H+Q-1) T .left (P:=P) (by omega) (by omega) sg (by rw [marks _ (by omega) le_rfl]; exact rt) rfl
  have ms:=sweepL m T H (Q-1) (P:=P) (by omega) sm (by
    intro i lo hi; rw [marks i lo (by omega)]; exact rm)
  rw [show H+(Q-1)=H+Q-1 by omega] at ms
  have last:=keep m out H H T .stay (P:=P) (by omega) (by omega) sm (by rw [th]; exact rn) rfl
  have whole:=one.append (two.append (gs.append (take.append (ms.append last))))
  convert whole using 1
  omega
private def FromHRows (entry out : Fin 7500) : Prop :=
  ∃ paid gap : Fin 7500, 4 ≤ entry.val ∧ 4 ≤ paid.val ∧ 4 ≤ gap.val ∧
    SerializedBody.machine.step entry none=(paid,none,.right) ∧
    SerializedBody.machine.step paid (some true)=(paid,some true,.right) ∧
    SerializedBody.machine.step paid none=(gap,none,.right) ∧
    SerializedBody.machine.step paid (some false)=(out,some false,.right) ∧
    SerializedBody.machine.step gap none=(gap,none,.right) ∧
    SerializedBody.machine.step gap (some false)=(out,some false,.right)
private theorem from_H {H Q F P T entry out} (positive : 0 < Q) (room : H+Q < F)
    (fit : F+1 ≤ P) (tf : T F=some false) (th : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none) (rows : FromHRows entry out) :
    Path P (F+1-H) ⟨entry,H,T⟩ ⟨out,F+1,T⟩ := by
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
private theorem paint_run {P : Nat} (q : Fin 7500) (T : Nat → Option Bool)
    (h w : Nat) (b : Bool) (fit : h+w ≤ P) (safe : 4 ≤ q.val)
    (occupied : ∀ i,h ≤ i → i < h+w → ∃ c,T i=some c)
    (row : ∀ c,SerializedBody.machine.step q (some c)=(q,some b,.right)) :
    Path P w ⟨q,h,T⟩ ⟨q,h+w,paint T h w b⟩ := by
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
private theorem Grid.painted {D T} (g : Grid D T) (j : Nat) (hj : j < 12) (b : Bool) :
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
private def ClearRows (j : Nat) (b : Bool) (start out : Fin 7500) : Prop :=
  ∃ e scan back : Fin 7500,4 ≤ e.val ∧ 4 ≤ scan.val ∧
    RouteR 0 j start e ∧ RouteL (j+1) 0 back out ∧
    SerializedBody.machine.step e none=(scan,none,.right) ∧
    (∀ c,SerializedBody.machine.step scan (some c)=(scan,some b,.right)) ∧
    SerializedBody.machine.step scan none=(back,none,.stay)
private theorem clear_run {D T P j b start out} (grid : Grid D T) (hj : j < 12)
    (fit : D 12 ≤ P) (code : ClearRows j b start out) :
    Path P (2*(D (j+1)-D 0+j)+2) ⟨start,D 0,T⟩
      ⟨out,D 0,paint T (D j+1) (D (j+1)-D j-1) b⟩ := by
  rcases code with ⟨e,scan,back,se,ss,route,ret,re,rs,rn⟩
  have rise:=grid.rise j hj
  have endpoint : D j+1+(D (j+1)-D j-1)=D (j+1) := by omega
  have room:=le_trans (grid.mono (j+1) 12 (by omega) le_rfl) fit
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
private def RestoreRows (b : Bool) (entry out : Fin 7500) : Prop :=
  ∃ hEnter sEnter seek back hBack : Fin 7500,
    ToHRows entry hEnter ∧ RouteL 2 0 hEnter sEnter ∧ RouteR 0 2 hBack out ∧
    4 ≤ sEnter.val ∧ 4 ≤ seek.val ∧ 4 ≤ back.val ∧
    SerializedBody.machine.step sEnter none=(seek,none,.left) ∧
    (∀ v,SerializedBody.machine.step seek (some v)=(seek,some v,.left)) ∧
    SerializedBody.machine.step seek none=(back,some b,.right) ∧
    (∀ v,SerializedBody.machine.step back (some v)=(back,some v,.right)) ∧
    SerializedBody.machine.step back none=(hBack,none,.stay)
private theorem restore_run {S L H Q F P c T b entry out}
    (sl : S < L) (lh : L < H) (physical : c < S)
    (positive : 0 < Q) (arena : H+Q < F) (fit : F+1 ≤ P)
    (ts : T S=none) (tl : T L=none) (th : T H=none)
    (td : T (F+1)=none) (tf : T F=some false) (hole : T c=none)
    (reg : ∀ i,S < i → i < L → ∃ v,T i=some v)
    (ass : ∀ i,L < i → i < H → ∃ v,T i=some v)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (src : ∀ i,c < i → i < S → ∃ v,T i=some v)
    (rows : RestoreRows b entry out) :
    Path P ((F+2-H)+(H-S+2)+(2*(S-c)+1)+(H-S+2)) ⟨entry,F+1,T⟩
      ⟨out,H,put T c (some b)⟩ := by
  rcases rows with ⟨hEnter,sEnter,seek,back,hBack,toH,hs,sh,se,ss,sb,re,rs,rt,rb,rn⟩
  let U:=put T c (some b)
  have routed:=(to_H positive arena fit td tf th marks gap toH).append
    (header_left sl lh (P:=P) (by omega) ts tl th reg ass hs)
  have one:=keep sEnter seek S (S-1) T .left (P:=P) (by omega) (by omega) se (by rw [ts];exact re) rfl
  have seekpath:=sweepL seek T c (S-1-c) (P:=P) (by omega) ss (by
    intro i lo hi;obtain ⟨v,hv⟩:=src i lo (by omega);rw [hv];exact rs v)
  rw [show c+(S-1-c)=S-1 by omega] at seekpath
  have take:=hop seek back c (c+1) T (some b) .right (P:=P) (by omega) (by omega) ss (by rw [hole];exact rt) rfl
  have ret:=sweepR back U (c+1) (S-(c+1)) (P:=P) (by omega) sb (by
    intro i lo hi
    have ne : i≠c := by omega
    obtain ⟨v,hv⟩:=src i (by omega) (by omega)
    simp only [U,put,if_neg ne];rw [hv];exact rb v)
  rw [show c+1+(S-(c+1))=S by omega] at ret
  have outside (i : Nat) (hi : S ≤ i) : U i=T i := by simp only [U,put,if_neg (by omega : i≠c)]
  have last:=keep back hBack S S U .stay (P:=P) (by omega) (by omega) sb (by rw [outside S le_rfl,ts];exact rn) rfl
  have suffix:=header_right sl lh (P:=P) (T:=U) (by omega)
    (by rw [outside S le_rfl];exact ts) (by rw [outside L (by omega)];exact tl)
    (by rw [outside H (by omega)];exact th)
    (by intro i lo hi;rw [outside i (by omega)];exact reg i lo hi)
    (by intro i lo hi;rw [outside i (by omega)];exact ass i lo hi) sh
  have whole:=routed.append (one.append (seekpath.append (take.append (ret.append (last.append suffix)))))
  convert whole using 1
  omega
private def scrub (D : Nat → Nat) : List (Nat × Bool) → (Nat → Option Bool) → (Nat → Option Bool)
  | [],T => T
  | (j,b)::xs,T => scrub D xs (paint T (D j+1) (D (j+1)-D j-1) b)
private def clearCost (D : Nat → Nat) : List (Nat × Bool) → Nat
  | [] => 0
  | (j,_)::xs => 2*(D (j+1)-D 0+j)+2+clearCost D xs
private inductive ClearPlan : List (Nat × Bool) → Fin 7500 → Fin 7500 → Prop
  | nil (q) : ClearPlan [] q q
  | cons {j b xs q mid out} : j < 12 → ClearRows j b q mid → ClearPlan xs mid out →
      ClearPlan ((j,b)::xs) q out
private theorem clear_plan {D T P edits start out} (grid : Grid D T) (fit : D 12 ≤ P)
    (plan : ClearPlan edits start out) :
    Path P (clearCost D edits) ⟨start,D 0,T⟩ ⟨out,D 0,scrub D edits T⟩ ∧
      Grid D (scrub D edits T) ∧ ∀ i,i < D 0 → scrub D edits T i=T i := by
  induction plan generalizing T with
  | nil q =>
    exact ⟨Path.nil _ (le_trans (grid.mono _ _ (by decide) (by decide)) fit),grid,by intro i _;rfl⟩
  | @cons j b xs q mid out hj code rest ih =>
    have one:=clear_run grid hj fit code
    obtain ⟨tail,gu,unchanged⟩:=ih (grid.painted j hj b)
    refine ⟨one.append tail,gu,?_⟩
    intro i hi
    rw [scrub,unchanged i hi]
    apply paint_outside
    have order:=grid.mono 0 j (by omega) (by omega)
    left;omega
private theorem clearCost_le {D P edits} (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (room : D 12 ≤ P) (bounded : ∀ jb ∈ edits,jb.1 < 12) :
    clearCost D edits ≤ edits.length*(2*P+24) := by
  induction edits with
  | nil => simp [clearCost]
  | cons jb xs ih =>
    rcases jb with ⟨j,b⟩
    have hj:=bounded (j,b) (by simp)
    have small : D (j+1) ≤ P := le_trans (mono _ _ (by omega) (by omega)) room
    have tail:=ih (by intro jb h;exact bounded jb (by simp [h]))
    simp only [clearCost,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
private def abortEdits : List (Nat × Bool) := [(1,false),(8,false),(6,false),(9,false),(10,true),(4,false),(5,false),(11,false)]
private theorem abortCost {D P T} (g : Grid D T) (room : D 12 ≤ P) :
    clearCost D abortEdits ≤ 16*P+192 := by
  have b : ∀ jb ∈ abortEdits,jb.1 < 12 := by decide
  calc
    clearCost D abortEdits ≤ abortEdits.length*(2*P+24) := clearCost_le g.mono room b
    _ = 16*P+192 := by change 8*(2*P+24)=16*P+192;omega
private def cleared (T : Nat → Option Bool) (D : Nat → Nat) : Nat → Option Bool := fun i =>
  if D 10 < i ∧ i < D 11 then some true else
  if [1,4,5,6,8,9,11].any (fun j => decide (D j < i ∧ i < D (j+1))) then some false else T i
private theorem paint_field {D : Nat → Nat} {T : Nat → Option Bool} {b : Bool} {j i : Nat} (rise : D j < D (j+1)) :
    paint T (D j+1) (D (j+1)-D j-1) b i=
      if D j < i ∧ i < D (j+1) then some b else T i := by
  have bound : D j+1+(D (j+1)-D j-1)=D (j+1) := by omega
  have eq : (D j+1 ≤ i ∧ i < D j+1+(D (j+1)-D j-1)) ↔ (D j < i ∧ i < D (j+1)) := by omega
  simp only [paint,eq]
private theorem field_disjoint {D T i j k} (g : Grid D T) (hj : j < 12) (hk : k < 12)
    (ne : j≠k) (inside : D k < i ∧ i < D (k+1)) : ¬(D j < i ∧ i < D (j+1)) := by
  by_cases before : j < k
  · have order:=g.mono (j+1) k (by omega) (by omega);omega
  · have order:=g.mono (k+1) j (by omega) (by omega);omega
private theorem scrub_abort {D T} (g : Grid D T) : scrub D abortEdits T=cleared T D := by
  funext i
  have step (T : Nat → Option Bool) (j : Nat) (b : Bool) (hj : j < 12) :=
    paint_field (T:=T) (b:=b) (i:=i) (g.rise j hj)
  simp only [scrub,abortEdits]
  simp only [step _ 1 _ (by decide),step _ 4 _ (by decide),step _ 5 _ (by decide),step _ 6 _ (by decide),step _ 8 _ (by decide),step _ 9 _ (by decide),step _ 10 _ (by decide),step _ 11 _ (by decide)]
  by_cases trueField : D 10 < i ∧ i < D 11
  · have other (j : Nat) (hj : j < 12) (ne : j≠10) := field_disjoint g hj (by decide : 10 < 12) ne trueField
    simp only [cleared,if_pos trueField,other 1 (by decide) (by decide),other 4 (by decide) (by decide),other 5 (by decide) (by decide),other 6 (by decide) (by decide),other 8 (by decide) (by decide),other 9 (by decide) (by decide),other 11 (by decide) (by decide),↓reduceIte]
  · simp only [cleared,List.any_cons,List.any_nil,Bool.or_eq_true,decide_eq_true_eq,if_neg trueField]
    by_cases a : D 1 < i ∧ i < D 2 <;> simp [a]
    by_cases b : D 4 < i ∧ i < D 5 <;> simp [b]
    by_cases c : D 5 < i ∧ i < D 6 <;> simp [c]
    by_cases d : D 6 < i ∧ i < D 7 <;> simp [d]
    by_cases e : D 8 < i ∧ i < D 9 <;> simp [e]
    by_cases f : D 9 < i ∧ i < D 10 <;> simp [f]
private def bm (b : Bool) : Fin 3 := ⟨if b then 1 else 0,by cases b <;> decide⟩
private def PhysicalAbort (b : Bool) : Prop :=
  ∃ start out : Fin 7500,
    SerializedBody.machine.step (SerializedBodyRefinement.getAbort (bm b)) none=(start,none,.stay) ∧
    ClearPlan abortEdits start out ∧ RestoreRows b out (st 1)
private def VirtualAbort : Prop :=
  ∃ start out : Fin 7500,
    SerializedBody.machine.step (SerializedBodyRefinement.getAbort ⟨2,by decide⟩) none=(start,none,.stay) ∧
    ClearPlan abortEdits start out ∧ ToHRows out (st 1)
private theorem abort_safe (m : Fin 3) : 4 ≤ (SerializedBodyRefinement.getAbort m).val := by
  fin_cases m <;> decide
private theorem abort_paths (physicalCode : ∀ b,PhysicalAbort b) (virtualCode : VirtualAbort)
    {D T S L H Q F c P} (source : Fin S → Bool)
    (grid : Grid D T) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (room : D 12 ≤ P)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    ∃ t,t ≤ 512*(P+1) ∧ Path P t
      ⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source c),D 0,T⟩
      ⟨st 1,H,fun i=>if c < S then if i=c then some (Pnp4.Frontier.ContractExpansion.padRead source c)
        else cleared T D i else cleared T D i⟩ := by
  have d0 : D 0 ≤ P := le_trans (grid.mono _ _ (by decide) (by decide)) room
  have hp : F+1 ≤ P := by omega
  by_cases pc : c < S
  · let bit:=source ⟨c,pc⟩
    have sm : SerializedBody.sourceMode source c=bm bit := by
      by_cases hb : source ⟨c,pc⟩=true <;> simp [SerializedBody.sourceMode,pc,bm,bit,hb]
    obtain ⟨start,out,row,plan,finish⟩:=physicalCode bit
    obtain ⟨path,gu,ext⟩:=clear_plan grid room plan
    let U:=scrub D abortEdits T
    have outside (i : Nat) (hi : i < D 0) : U i=T i := ext i hi
    have jump:=keep (SerializedBodyRefinement.getAbort (bm bit)) start (D 0) (D 0) T .stay (P:=P) d0 d0 (abort_safe _) (by rw [grid.blank 0 (by decide)];exact row) rfl
    have restored:=restore_run (T:=U) sl lh pc positive arena hp
      (by rw [outside S (by omega)];exact ts) (by rw [outside L (by omega)];exact tl)
      (by rw [outside H (by omega)];exact th)
      (by rw [←anchor];exact gu.blank 0 (by decide)) (by rw [outside F (by omega)];exact tf)
      (by rw [outside c (by omega)];exact hole pc)
      (by intro i lo hi;rw [outside i (by omega)];exact reg i lo hi)
      (by intro i lo hi;rw [outside i (by omega)];exact ass i lo hi)
      (by intro i lo hi;rw [outside i (by omega)];exact marks i lo hi)
      (by intro i lo hi;rw [outside i (by omega)];exact gap i lo hi)
      (by intro i lo hi;rw [outside i (by omega)];exact ⟨_,src i lo hi⟩) finish
    rw [←anchor] at restored
    have whole:=jump.append (path.append restored)
    refine ⟨1+(clearCost D abortEdits+((F+2-H)+(H-S+2)+(2*(S-c)+1)+(H-S+2))),?_,?_⟩
    · have bound:=abortCost grid room;omega
    · simpa only [sm,pc,↓reduceIte,put,U,scrub_abort grid,bit,Pnp4.Frontier.ContractExpansion.padRead,↓reduceDIte] using whole
  · obtain ⟨start,out,row,plan,finish⟩:=virtualCode
    obtain ⟨path,gu,ext⟩:=clear_plan grid room plan
    let U:=scrub D abortEdits T
    have outside (i : Nat) (hi : i < D 0) : U i=T i := ext i hi
    have jump:=keep (SerializedBodyRefinement.getAbort ⟨2,by decide⟩) start (D 0) (D 0) T .stay (P:=P) d0 d0 (abort_safe _) (by rw [grid.blank 0 (by decide)];exact row) rfl
    have restored:=to_H (T:=U) positive arena hp
      (by rw [←anchor];exact gu.blank 0 (by decide)) (by rw [outside F (by omega)];exact tf)
      (by rw [outside H (by omega)];exact th)
      (by intro i lo hi;rw [outside i (by omega)];exact marks i lo hi)
      (by intro i lo hi;rw [outside i (by omega)];exact gap i lo hi) finish
    rw [←anchor] at restored
    have whole:=jump.append (path.append restored)
    refine ⟨1+(clearCost D abortEdits+(F+2-H)),?_,?_⟩
    · have bound:=abortCost grid room;omega
    · simpa only [SerializedBody.sourceMode,pc,↓reduceDIte,↓reduceIte,U,scrub_abort grid] using whole
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

private def EntryRows (m : Fin 3) : Prop :=
  ∃ scan need de pos : Fin 7500,
    SerializedBody.machine.step (SerializedBody.entry m) none=(scan,none,.stay) ∧
    FromHRows scan need ∧ 4 ≤ need.val ∧
    SerializedBody.machine.step need none=(de,none,.stay) ∧
    DecRows 6 de (SerializedBodyRefinement.getAbort m) pos
private theorem zero_path (entryCode : ∀ m,EntryRows m)
    {D T S H Q F c P} (source : Fin S → Bool)
    (grid : Grid D T) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (room : D 12 ≤ P) (quota : ∀ i,D 6 < i → i < D 7 → T i=some false)
    (th : T H=none) (tf : T F=some false)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none) :
    Path P (1+(F+1-H)+1+(2*(D 6-D 0+6)+3))
      ⟨SerializedBody.entry (SerializedBody.sourceMode source c),H,T⟩
      ⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source c),D 0,T⟩ := by
  let m:=SerializedBody.sourceMode source c
  obtain ⟨scan,need,de,pos,row,fromH,sn,needRow,dec⟩:=entryCode m
  have d0 : D 0 ≤ P := le_trans (grid.mono _ _ (by decide) (by decide)) room
  have hp : F+1 ≤ P := by omega
  have first:=keep (SerializedBody.entry m) scan H H T .stay (P:=P) (by omega) (by omega)
    (by change 4 ≤ (4+m.val)%7500;have :=m.isLt;omega) (by rw [th];exact row) rfl
  have body:=from_H positive arena hp tf th marks gap fromH
  rw [←anchor] at body
  have jump:=keep need de (D 0) (D 0) T .stay (P:=P) d0 d0 sn (by rw [grid.blank 0 (by decide)];exact needRow) rfl
  have un : Unary D T 6 0 := by
    intro i lo hi;rw [quota i lo hi];simp only [show ¬i-D 6 ≤ 0 by omega,decide_false]
  have length : D 7=D 6+(D 7-D 6-1)+1 := by
    have hh : D 6 < D 7 := grid.rise 6 (by decide)
    omega
  have last:=dec_zero grid (by decide) room length un dec
  have whole:=first.append (body.append (jump.append last))
  convert whole using 1
  omega
private theorem cleanup_result (physicalCode : ∀ b,PhysicalAbort b) (virtualCode : VirtualAbort)
    (D : Nat → Nat) (T : Nat → Option Bool) (S L H Q F c N B P : Nat) (source : Fin S → Bool)
    (grid : Grid D T) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (room : D 12 ≤ P) (fit : P < tapeLength N B)
    (h0 : D 0 < tapeLength N B) (hH : H < tapeLength N B)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let initial : Config 7500 N B:=⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source c),⟨D 0,h0⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 512*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else cleared T D i.val else cleared T D i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  obtain ⟨t,price,path⟩:=abort_paths physicalCode virtualCode source grid sl lh positive arena anchor room ts tl th tf reg ass marks gap hole src
  refine ⟨t,price,?_,?_⟩
  · simpa only [embed] using path.execute fit
  · simpa only [embed] using path.prefix fit
private theorem zero_result (physicalCode : ∀ b,PhysicalAbort b) (virtualCode : VirtualAbort)
    (entryCode : ∀ m,EntryRows m)
    (D : Nat → Nat) (T : Nat → Option Bool) (S L H Q F c N B P : Nat) (source : Fin S → Bool)
    (grid : Grid D T) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (room : D 12 ≤ P) (fit : P < tapeLength N B)
    (hH : H < tapeLength N B) (quota : ∀ i,D 6 < i → i < D 7 → T i=some false)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let initial : Config 7500 N B:=⟨SerializedBody.entry (SerializedBody.sourceMode source c),⟨H,hH⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 1024*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else cleared T D i.val else cleared T D i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  obtain ⟨t,price,tail⟩:=abort_paths physicalCode virtualCode source grid sl lh positive arena anchor room ts tl th tf reg ass marks gap hole src
  have front:=zero_path entryCode (c:=c) source grid positive arena anchor room quota th tf marks gap
  have whole:=front.append tail
  refine ⟨(1+(F+1-H)+1+(2*(D 6-D 0+6)+3))+t,?_,?_,?_⟩
  · have d6 : D 6 ≤ P := le_trans (grid.mono _ _ (by decide) (by decide)) room
    have d0 : D 0 ≤ P := le_trans (grid.mono _ _ (by decide) (by decide)) room
    omega
  · simpa only [embed] using whole.execute fit
  · simpa only [embed] using whole.prefix fit
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
def needEntry (mode : Fin 3) : Fin 7500 := st (#[337,3362,5740][mode.val]!)
private def pin_needEntry : Fin 3 → Fin 7500 := needEntry
#print axioms SerializedBodyCompletion.needEntry
#print axioms pin_needEntry
private def NeedRows (m : Fin 3) : Prop :=
  ∃ de inc tag : Fin 7500,
    SerializedBody.machine.step (needEntry m) none=(de,none,.stay) ∧
    DecRows 6 de (SerializedBodyRefinement.getAbort m) inc ∧ IncRows 5 inc tag ∧
    4 ≤ tag.val ∧ SerializedBody.machine.step tag none=(SerializedBodyRefinement.getEntry ⟨0,by decide⟩ m,none,.stay)
private def EntryDirect (m : Fin 3) : Prop :=
  ∃ scan : Fin 7500,SerializedBody.machine.step (SerializedBody.entry m) none=(scan,none,.stay) ∧ FromHRows scan (needEntry m)
private theorem need_path (code : ∀ m,NeedRows m) (mode : Fin 3) {D T P r q v}
    (grid : Grid D T) (room : D 12 ≤ P) (positive : 0 < q) (bound : q+v ≤ r)
    (len5 : D 6=D 5+r+1) (len6 : D 7=D 6+r+1)
    (quota : Unary D T 6 q) (nodes : Unary D T 5 v) :
    Path P (1+(2*(D 6-D 0+6)+2*q+4)+(2*(D 5-D 0+5)+2*v+4)+1)
      ⟨needEntry mode,D 0,T⟩ ⟨SerializedBodyRefinement.getEntry ⟨0,by decide⟩ mode,D 0,
        fun i=>if i=D 5+v+1 then some true else if i=D 6+q then some false else T i⟩ := by
  obtain ⟨de,inc,tag,row,dec,ic,safe,lastRow⟩:=code mode
  have d0 : D 0 ≤ P := le_trans (grid.mono _ _ (by decide) (by decide)) room
  have safeNeed : 4 ≤ (needEntry mode).val := by fin_cases mode <;> decide
  have jump:=keep (needEntry mode) de (D 0) (D 0) T .stay (P:=P) d0 d0 safeNeed (by rw [grid.blank 0 (by decide)];exact row) rfl
  have old:=unary_true quota len6 (by omega) (i:=D 6+q) (by omega) le_rfl
  let U:=put T (D 6+q) (some false)
  have gu : Grid D U:=grid.change_some _ true false old
  have decrement:=dec_positive grid (by decide) room len6 quota positive (by omega) dec
  have nodes' : Unary D U 5 v := by
    intro i lo hi
    change i < D 6 at hi
    have ne : i≠D 6+q := by omega
    simp only [U,put,if_neg ne];exact nodes i lo hi
  have increment:=inc_success gu (by decide) room len5 nodes' (by omega) ic
  let V:=put U (D 5+v+1) (some true)
  have nodeOld : U (D 5+v+1)=some false := by
    rw [nodes' _ (by omega) (by change D 5+v+1 < D 6;omega)]
    simp [show ¬D 5+v+1-D 5 ≤ v by omega]
  have gv : Grid D V:=gu.change_some _ false true nodeOld
  have last:=keep tag (SerializedBodyRefinement.getEntry ⟨0,by decide⟩ mode) (D 0) (D 0) V .stay (P:=P) d0 d0 safe (by rw [gv.blank 0 (by decide)];exact lastRow) rfl
  have whole:=jump.append (decrement.append (increment.append last))
  convert whole using 1
  omega
private theorem entry_result (code : ∀ m,EntryDirect m) (mode : Fin 3)
    (T : Nat → Option Bool) (H Q F N B P : Nat) (positive : 0 < Q) (arena : H+Q < F)
    (room : F+1 ≤ P) (fit : P < tapeLength N B)
    (hH : H < tapeLength N B) (h0 : F+1 < tapeLength N B)
    (th : T H=none) (tf : T F=some false)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none) :
    let initial : Config 7500 N B:=⟨SerializedBody.entry mode,⟨H,hH⟩,fun i=>T i.val⟩
    SerializedBody.machine.run (F+2-H) initial=⟨needEntry mode,⟨F+1,h0⟩,fun i=>T i.val⟩ ∧
      ∀ u,u ≤ F+2-H → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  obtain ⟨scan,row,fromH⟩:=code mode
  have one:=keep (SerializedBody.entry mode) scan H H T .stay (P:=P) (by omega) (by omega)
    (by change 4 ≤ (4+mode.val)%7500;have :=mode.isLt;omega) (by rw [th];exact row) rfl
  have rest:=from_H positive arena room tf th marks gap fromH
  have path:=one.append rest
  rw [show 1+(F+1-H)=F+2-H by omega] at path
  have last : 4 ≤ (needEntry mode).val := by fin_cases mode <;> decide
  have native:=path.execute fit
  dsimp only [embed] at native
  constructor
  · exact native
  · intro u hu
    by_cases endAt : u=F+2-H
    · subst u;rw [native];exact last
    · exact path.prefix fit u (by omega)
private theorem need_result (code : ∀ m,NeedRows m) (mode : Fin 3)
    (D : Nat → Nat) (T : Nat → Option Bool) (r q v N B P : Nat)
    (grid : Grid D T) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B)
    (positive : 0 < q) (bound : q+v ≤ r) (len5 : D 6=D 5+r+1) (len6 : D 7=D 6+r+1)
    (quota : ∀ i,D 6 < i → i < D 7 → T i=some (decide (i-D 6 ≤ q)))
    (nodes : ∀ i,D 5 < i → i < D 6 → T i=some (decide (i-D 5 ≤ v))) :
    let ticks:=1+(2*(D 6-D 0+6)+2*q+4)+(2*(D 5-D 0+5)+2*v+4)+1
    let initial : Config 7500 N B:=⟨needEntry mode,⟨D 0,h0⟩,fun i=>T i.val⟩
    ticks ≤ 128*(P+1) ∧ SerializedBody.machine.run ticks initial=
      ⟨SerializedBodyRefinement.getEntry ⟨0,by decide⟩ mode,⟨D 0,h0⟩,
        fun i=>if i.val=D 5+v+1 then some true else if i.val=D 6+q then some false else T i.val⟩ ∧
      ∀ u,u ≤ ticks → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  have path:=need_path code mode grid room positive bound len5 len6 quota nodes
  have native:=path.execute fit
  dsimp only [embed] at native
  dsimp only
  refine ⟨?_,?_,?_⟩
  · have d5 : D 5 ≤ P := le_trans (grid.mono _ _ (by decide) (by decide)) room
    have d6 : D 6 ≤ P := le_trans (grid.mono _ _ (by decide) (by decide)) room
    omega
  · exact native
  · intro u hu
    by_cases endAt : u=1+(2*(D 6-D 0+6)+2*q+4)+(2*(D 5-D 0+5)+2*v+4)+1
    · subst u;rw [native]
      change 4 ≤ (SerializedBodyRefinement.getEntry ⟨0,by decide⟩ mode).val
      fin_cases mode <;> decide
    · exact path.prefix fit u (by omega)

section LiteralRows
set_option maxRecDepth 4000
private theorem cl0 : ClearRows 1 false (st 269) (st 261) := by
  exact ⟨(st 267),(st 266),(st 265),by decide,by decide,
    (RouteR.next (s:=(st 268)) (q:=(st 267)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 1 (st 267))),
    (RouteL.next (s:=(st 264)) (q:=(st 263)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 262)) (q:=(st 261)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 261)))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl1 : ClearRows 8 false (st 261) (st 225) := by
  exact ⟨(st 245),(st 244),(st 243),by decide,by decide,
    (RouteR.next (s:=(st 260)) (q:=(st 259)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 258)) (q:=(st 257)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 256)) (q:=(st 255)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 254)) (q:=(st 253)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 252)) (q:=(st 251)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 250)) (q:=(st 249)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 248)) (q:=(st 247)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 246)) (q:=(st 245)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 8 (st 245)))))))))),
    (RouteL.next (s:=(st 242)) (q:=(st 241)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 240)) (q:=(st 239)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 238)) (q:=(st 237)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 236)) (q:=(st 235)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 234)) (q:=(st 233)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 232)) (q:=(st 231)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 230)) (q:=(st 229)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 228)) (q:=(st 227)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 226)) (q:=(st 225)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 225))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl2 : ClearRows 6 false (st 225) (st 197) := by
  exact ⟨(st 213),(st 212),(st 211),by decide,by decide,
    (RouteR.next (s:=(st 224)) (q:=(st 223)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 222)) (q:=(st 221)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 220)) (q:=(st 219)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 218)) (q:=(st 217)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 216)) (q:=(st 215)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 214)) (q:=(st 213)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 6 (st 213)))))))),
    (RouteL.next (s:=(st 210)) (q:=(st 209)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 208)) (q:=(st 207)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 206)) (q:=(st 205)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 204)) (q:=(st 203)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 202)) (q:=(st 201)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 200)) (q:=(st 199)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 198)) (q:=(st 197)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 197))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl3 : ClearRows 9 false (st 197) (st 157) := by
  exact ⟨(st 179),(st 178),(st 177),by decide,by decide,
    (RouteR.next (s:=(st 196)) (q:=(st 195)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 194)) (q:=(st 193)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 192)) (q:=(st 191)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 190)) (q:=(st 189)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 188)) (q:=(st 187)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 186)) (q:=(st 185)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 184)) (q:=(st 183)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 182)) (q:=(st 181)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 180)) (q:=(st 179)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 9 (st 179))))))))))),
    (RouteL.next (s:=(st 176)) (q:=(st 175)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 174)) (q:=(st 173)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 172)) (q:=(st 171)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 170)) (q:=(st 169)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 168)) (q:=(st 167)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 166)) (q:=(st 165)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 164)) (q:=(st 163)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 162)) (q:=(st 161)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 160)) (q:=(st 159)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 158)) (q:=(st 157)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 157)))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl4 : ClearRows 10 true (st 157) (st 113) := by
  exact ⟨(st 137),(st 136),(st 135),by decide,by decide,
    (RouteR.next (s:=(st 156)) (q:=(st 155)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 154)) (q:=(st 153)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 152)) (q:=(st 151)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 150)) (q:=(st 149)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 148)) (q:=(st 147)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 146)) (q:=(st 145)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 144)) (q:=(st 143)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 142)) (q:=(st 141)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 140)) (q:=(st 139)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 138)) (q:=(st 137)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 10 (st 137)))))))))))),
    (RouteL.next (s:=(st 134)) (q:=(st 133)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 132)) (q:=(st 131)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 130)) (q:=(st 129)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 128)) (q:=(st 127)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 126)) (q:=(st 125)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 124)) (q:=(st 123)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 122)) (q:=(st 121)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 120)) (q:=(st 119)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 118)) (q:=(st 117)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 116)) (q:=(st 115)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 114)) (q:=(st 113)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 113))))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl5 : ClearRows 4 false (st 113) (st 93) := by
  exact ⟨(st 105),(st 104),(st 103),by decide,by decide,
    (RouteR.next (s:=(st 112)) (q:=(st 111)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 110)) (q:=(st 109)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 108)) (q:=(st 107)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 106)) (q:=(st 105)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 105)))))),
    (RouteL.next (s:=(st 102)) (q:=(st 101)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 100)) (q:=(st 99)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 98)) (q:=(st 97)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 96)) (q:=(st 95)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 94)) (q:=(st 93)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 93))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl6 : ClearRows 5 false (st 93) (st 69) := by
  exact ⟨(st 83),(st 82),(st 81),by decide,by decide,
    (RouteR.next (s:=(st 92)) (q:=(st 91)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 90)) (q:=(st 89)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 88)) (q:=(st 87)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 86)) (q:=(st 85)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 84)) (q:=(st 83)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 5 (st 83))))))),
    (RouteL.next (s:=(st 80)) (q:=(st 79)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 78)) (q:=(st 77)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 76)) (q:=(st 75)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 74)) (q:=(st 73)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 72)) (q:=(st 71)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 70)) (q:=(st 69)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 69)))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl7 : ClearRows 11 false (st 69) (st 21) := by
  exact ⟨(st 47),(st 46),(st 45),by decide,by decide,
    (RouteR.next (s:=(st 68)) (q:=(st 67)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 66)) (q:=(st 65)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 64)) (q:=(st 63)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 62)) (q:=(st 61)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 60)) (q:=(st 59)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 58)) (q:=(st 57)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 56)) (q:=(st 55)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 54)) (q:=(st 53)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 52)) (q:=(st 51)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 50)) (q:=(st 49)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 48)) (q:=(st 47)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 47))))))))))))),
    (RouteL.next (s:=(st 44)) (q:=(st 43)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 42)) (q:=(st 41)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 40)) (q:=(st 39)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 38)) (q:=(st 37)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 36)) (q:=(st 35)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 34)) (q:=(st 33)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 32)) (q:=(st 31)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 30)) (q:=(st 29)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 28)) (q:=(st 27)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 26)) (q:=(st 25)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 24)) (q:=(st 23)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 22)) (q:=(st 21)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 21)))))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem toh0 : ToHRows (st 21) (st 17) := by
  exact ⟨(st 20),(st 19),(st 18),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem rs0 : RestoreRows false (st 21) (st 1) := by
  exact ⟨(st 17),(st 13),(st 12),(st 11),(st 10),toh0,
    (RouteL.next (s:=(st 14)) (q:=(st 16)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 15)) (q:=(st 13)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 13)))),
    (RouteR.next (s:=(st 8)) (q:=(st 9)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7)) (q:=(st 1)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1)))),by decide,by decide,by decide,rfl,(by intro b;cases b <;> rfl),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem plan0 : ClearPlan abortEdits (st 269) (st 21) := by
  exact ClearPlan.cons (by decide) cl0 (ClearPlan.cons (by decide) cl1 (ClearPlan.cons (by decide) cl2 (ClearPlan.cons (by decide) cl3 (ClearPlan.cons (by decide) cl4 (ClearPlan.cons (by decide) cl5 (ClearPlan.cons (by decide) cl6 (ClearPlan.cons (by decide) cl7 (ClearPlan.nil (st 21)))))))))

private theorem abort_row0 : SerializedBody.machine.step (SerializedBodyRefinement.getAbort ⟨0,by decide⟩) none=((st 269),none,.stay) := by rfl

private theorem cl8 : ClearRows 1 false (st 3306) (st 3298) := by
  exact ⟨(st 3304),(st 3303),(st 3302),by decide,by decide,
    (RouteR.next (s:=(st 3305)) (q:=(st 3304)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 1 (st 3304))),
    (RouteL.next (s:=(st 3301)) (q:=(st 3300)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3299)) (q:=(st 3298)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3298)))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl9 : ClearRows 8 false (st 3298) (st 3262) := by
  exact ⟨(st 3282),(st 3281),(st 3280),by decide,by decide,
    (RouteR.next (s:=(st 3297)) (q:=(st 3296)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3295)) (q:=(st 3294)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3293)) (q:=(st 3292)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3291)) (q:=(st 3290)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3289)) (q:=(st 3288)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3287)) (q:=(st 3286)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3285)) (q:=(st 3284)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3283)) (q:=(st 3282)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 8 (st 3282)))))))))),
    (RouteL.next (s:=(st 3279)) (q:=(st 3278)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3277)) (q:=(st 3276)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3275)) (q:=(st 3274)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3273)) (q:=(st 3272)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3271)) (q:=(st 3270)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3269)) (q:=(st 3268)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3267)) (q:=(st 3266)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3265)) (q:=(st 3264)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3263)) (q:=(st 3262)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3262))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl10 : ClearRows 6 false (st 3262) (st 3234) := by
  exact ⟨(st 3250),(st 3249),(st 3248),by decide,by decide,
    (RouteR.next (s:=(st 3261)) (q:=(st 3260)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3259)) (q:=(st 3258)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3257)) (q:=(st 3256)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3255)) (q:=(st 3254)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3253)) (q:=(st 3252)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3251)) (q:=(st 3250)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 6 (st 3250)))))))),
    (RouteL.next (s:=(st 3247)) (q:=(st 3246)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3245)) (q:=(st 3244)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3243)) (q:=(st 3242)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3241)) (q:=(st 3240)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3239)) (q:=(st 3238)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3237)) (q:=(st 3236)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3235)) (q:=(st 3234)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3234))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl11 : ClearRows 9 false (st 3234) (st 3194) := by
  exact ⟨(st 3216),(st 3215),(st 3214),by decide,by decide,
    (RouteR.next (s:=(st 3233)) (q:=(st 3232)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3231)) (q:=(st 3230)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3229)) (q:=(st 3228)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3227)) (q:=(st 3226)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3225)) (q:=(st 3224)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3223)) (q:=(st 3222)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3221)) (q:=(st 3220)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3219)) (q:=(st 3218)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3217)) (q:=(st 3216)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 9 (st 3216))))))))))),
    (RouteL.next (s:=(st 3213)) (q:=(st 3212)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3211)) (q:=(st 3210)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3209)) (q:=(st 3208)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3207)) (q:=(st 3206)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3205)) (q:=(st 3204)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3203)) (q:=(st 3202)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3201)) (q:=(st 3200)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3199)) (q:=(st 3198)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3197)) (q:=(st 3196)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3195)) (q:=(st 3194)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3194)))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl12 : ClearRows 10 true (st 3194) (st 3150) := by
  exact ⟨(st 3174),(st 3173),(st 3172),by decide,by decide,
    (RouteR.next (s:=(st 3193)) (q:=(st 3192)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3191)) (q:=(st 3190)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3189)) (q:=(st 3188)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3187)) (q:=(st 3186)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3185)) (q:=(st 3184)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3183)) (q:=(st 3182)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3181)) (q:=(st 3180)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3179)) (q:=(st 3178)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3177)) (q:=(st 3176)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3175)) (q:=(st 3174)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 10 (st 3174)))))))))))),
    (RouteL.next (s:=(st 3171)) (q:=(st 3170)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3169)) (q:=(st 3168)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3167)) (q:=(st 3166)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3165)) (q:=(st 3164)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3163)) (q:=(st 3162)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3161)) (q:=(st 3160)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3159)) (q:=(st 3158)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3157)) (q:=(st 3156)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3155)) (q:=(st 3154)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3153)) (q:=(st 3152)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3151)) (q:=(st 3150)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3150))))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl13 : ClearRows 4 false (st 3150) (st 3130) := by
  exact ⟨(st 3142),(st 3141),(st 3140),by decide,by decide,
    (RouteR.next (s:=(st 3149)) (q:=(st 3148)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3147)) (q:=(st 3146)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3145)) (q:=(st 3144)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3143)) (q:=(st 3142)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 3142)))))),
    (RouteL.next (s:=(st 3139)) (q:=(st 3138)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3137)) (q:=(st 3136)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3135)) (q:=(st 3134)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3133)) (q:=(st 3132)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3131)) (q:=(st 3130)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3130))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl14 : ClearRows 5 false (st 3130) (st 3106) := by
  exact ⟨(st 3120),(st 3119),(st 3118),by decide,by decide,
    (RouteR.next (s:=(st 3129)) (q:=(st 3128)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3127)) (q:=(st 3126)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3125)) (q:=(st 3124)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3123)) (q:=(st 3122)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3121)) (q:=(st 3120)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 5 (st 3120))))))),
    (RouteL.next (s:=(st 3117)) (q:=(st 3116)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3115)) (q:=(st 3114)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3113)) (q:=(st 3112)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3111)) (q:=(st 3110)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3109)) (q:=(st 3108)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3107)) (q:=(st 3106)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3106)))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl15 : ClearRows 11 false (st 3106) (st 3058) := by
  exact ⟨(st 3084),(st 3083),(st 3082),by decide,by decide,
    (RouteR.next (s:=(st 3105)) (q:=(st 3104)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3103)) (q:=(st 3102)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3101)) (q:=(st 3100)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3099)) (q:=(st 3098)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3097)) (q:=(st 3096)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3095)) (q:=(st 3094)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3093)) (q:=(st 3092)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3091)) (q:=(st 3090)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3089)) (q:=(st 3088)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3087)) (q:=(st 3086)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3085)) (q:=(st 3084)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 3084))))))))))))),
    (RouteL.next (s:=(st 3081)) (q:=(st 3080)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3079)) (q:=(st 3078)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3077)) (q:=(st 3076)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3075)) (q:=(st 3074)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3073)) (q:=(st 3072)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3071)) (q:=(st 3070)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3069)) (q:=(st 3068)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3067)) (q:=(st 3066)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3065)) (q:=(st 3064)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3063)) (q:=(st 3062)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3061)) (q:=(st 3060)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3059)) (q:=(st 3058)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3058)))))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem toh1 : ToHRows (st 3058) (st 3054) := by
  exact ⟨(st 3057),(st 3056),(st 3055),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem rs1 : RestoreRows true (st 3058) (st 1) := by
  exact ⟨(st 3054),(st 3050),(st 3049),(st 11),(st 10),toh1,
    (RouteL.next (s:=(st 3051)) (q:=(st 3053)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3052)) (q:=(st 3050)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3050)))),
    (RouteR.next (s:=(st 8)) (q:=(st 9)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 7)) (q:=(st 1)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1)))),by decide,by decide,by decide,rfl,(by intro b;cases b <;> rfl),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem plan1 : ClearPlan abortEdits (st 3306) (st 3058) := by
  exact ClearPlan.cons (by decide) cl8 (ClearPlan.cons (by decide) cl9 (ClearPlan.cons (by decide) cl10 (ClearPlan.cons (by decide) cl11 (ClearPlan.cons (by decide) cl12 (ClearPlan.cons (by decide) cl13 (ClearPlan.cons (by decide) cl14 (ClearPlan.cons (by decide) cl15 (ClearPlan.nil (st 3058)))))))))

private theorem abort_row1 : SerializedBody.machine.step (SerializedBodyRefinement.getAbort ⟨1,by decide⟩) none=((st 3306),none,.stay) := by rfl

private theorem cl16 : ClearRows 1 false (st 5684) (st 5676) := by
  exact ⟨(st 5682),(st 5681),(st 5680),by decide,by decide,
    (RouteR.next (s:=(st 5683)) (q:=(st 5682)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 1 (st 5682))),
    (RouteL.next (s:=(st 5679)) (q:=(st 5678)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5677)) (q:=(st 5676)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5676)))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl17 : ClearRows 8 false (st 5676) (st 5640) := by
  exact ⟨(st 5660),(st 5659),(st 5658),by decide,by decide,
    (RouteR.next (s:=(st 5675)) (q:=(st 5674)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5673)) (q:=(st 5672)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5671)) (q:=(st 5670)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5669)) (q:=(st 5668)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5667)) (q:=(st 5666)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5665)) (q:=(st 5664)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5663)) (q:=(st 5662)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5661)) (q:=(st 5660)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 8 (st 5660)))))))))),
    (RouteL.next (s:=(st 5657)) (q:=(st 5656)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5655)) (q:=(st 5654)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5653)) (q:=(st 5652)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5651)) (q:=(st 5650)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5649)) (q:=(st 5648)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5647)) (q:=(st 5646)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5645)) (q:=(st 5644)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5643)) (q:=(st 5642)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5641)) (q:=(st 5640)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5640))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl18 : ClearRows 6 false (st 5640) (st 5612) := by
  exact ⟨(st 5628),(st 5627),(st 5626),by decide,by decide,
    (RouteR.next (s:=(st 5639)) (q:=(st 5638)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5637)) (q:=(st 5636)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5635)) (q:=(st 5634)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5633)) (q:=(st 5632)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5631)) (q:=(st 5630)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5629)) (q:=(st 5628)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 6 (st 5628)))))))),
    (RouteL.next (s:=(st 5625)) (q:=(st 5624)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5623)) (q:=(st 5622)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5621)) (q:=(st 5620)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5619)) (q:=(st 5618)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5617)) (q:=(st 5616)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5615)) (q:=(st 5614)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5613)) (q:=(st 5612)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5612))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl19 : ClearRows 9 false (st 5612) (st 5572) := by
  exact ⟨(st 5594),(st 5593),(st 5592),by decide,by decide,
    (RouteR.next (s:=(st 5611)) (q:=(st 5610)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5609)) (q:=(st 5608)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5607)) (q:=(st 5606)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5605)) (q:=(st 5604)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5603)) (q:=(st 5602)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5601)) (q:=(st 5600)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5599)) (q:=(st 5598)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5597)) (q:=(st 5596)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5595)) (q:=(st 5594)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 9 (st 5594))))))))))),
    (RouteL.next (s:=(st 5591)) (q:=(st 5590)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5589)) (q:=(st 5588)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5587)) (q:=(st 5586)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5585)) (q:=(st 5584)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5583)) (q:=(st 5582)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5581)) (q:=(st 5580)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5579)) (q:=(st 5578)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5577)) (q:=(st 5576)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5575)) (q:=(st 5574)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5573)) (q:=(st 5572)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5572)))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl20 : ClearRows 10 true (st 5572) (st 5528) := by
  exact ⟨(st 5552),(st 5551),(st 5550),by decide,by decide,
    (RouteR.next (s:=(st 5571)) (q:=(st 5570)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5569)) (q:=(st 5568)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5567)) (q:=(st 5566)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5565)) (q:=(st 5564)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5563)) (q:=(st 5562)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5561)) (q:=(st 5560)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5559)) (q:=(st 5558)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5557)) (q:=(st 5556)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5555)) (q:=(st 5554)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5553)) (q:=(st 5552)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 10 (st 5552)))))))))))),
    (RouteL.next (s:=(st 5549)) (q:=(st 5548)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5547)) (q:=(st 5546)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5545)) (q:=(st 5544)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5543)) (q:=(st 5542)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5541)) (q:=(st 5540)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5539)) (q:=(st 5538)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5537)) (q:=(st 5536)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5535)) (q:=(st 5534)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5533)) (q:=(st 5532)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5531)) (q:=(st 5530)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5529)) (q:=(st 5528)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5528))))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl21 : ClearRows 4 false (st 5528) (st 5508) := by
  exact ⟨(st 5520),(st 5519),(st 5518),by decide,by decide,
    (RouteR.next (s:=(st 5527)) (q:=(st 5526)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5525)) (q:=(st 5524)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5523)) (q:=(st 5522)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5521)) (q:=(st 5520)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 4 (st 5520)))))),
    (RouteL.next (s:=(st 5517)) (q:=(st 5516)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5515)) (q:=(st 5514)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5513)) (q:=(st 5512)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5511)) (q:=(st 5510)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5509)) (q:=(st 5508)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5508))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl22 : ClearRows 5 false (st 5508) (st 5484) := by
  exact ⟨(st 5498),(st 5497),(st 5496),by decide,by decide,
    (RouteR.next (s:=(st 5507)) (q:=(st 5506)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5505)) (q:=(st 5504)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5503)) (q:=(st 5502)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5501)) (q:=(st 5500)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5499)) (q:=(st 5498)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 5 (st 5498))))))),
    (RouteL.next (s:=(st 5495)) (q:=(st 5494)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5493)) (q:=(st 5492)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5491)) (q:=(st 5490)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5489)) (q:=(st 5488)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5487)) (q:=(st 5486)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5485)) (q:=(st 5484)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5484)))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem cl23 : ClearRows 11 false (st 5484) (st 5436) := by
  exact ⟨(st 5462),(st 5461),(st 5460),by decide,by decide,
    (RouteR.next (s:=(st 5483)) (q:=(st 5482)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5481)) (q:=(st 5480)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5479)) (q:=(st 5478)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5477)) (q:=(st 5476)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5475)) (q:=(st 5474)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5473)) (q:=(st 5472)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5471)) (q:=(st 5470)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5469)) (q:=(st 5468)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5467)) (q:=(st 5466)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5465)) (q:=(st 5464)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5463)) (q:=(st 5462)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 11 (st 5462))))))))))))),
    (RouteL.next (s:=(st 5459)) (q:=(st 5458)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5457)) (q:=(st 5456)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5455)) (q:=(st 5454)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5453)) (q:=(st 5452)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5451)) (q:=(st 5450)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5449)) (q:=(st 5448)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5447)) (q:=(st 5446)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5445)) (q:=(st 5444)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5443)) (q:=(st 5442)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5441)) (q:=(st 5440)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5439)) (q:=(st 5438)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5437)) (q:=(st 5436)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5436)))))))))))))),rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem toh2 : ToHRows (st 5436) (st 1) := by
  exact ⟨(st 5435),(st 5434),(st 5433),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem plan2 : ClearPlan abortEdits (st 5684) (st 5436) := by
  exact ClearPlan.cons (by decide) cl16 (ClearPlan.cons (by decide) cl17 (ClearPlan.cons (by decide) cl18 (ClearPlan.cons (by decide) cl19 (ClearPlan.cons (by decide) cl20 (ClearPlan.cons (by decide) cl21 (ClearPlan.cons (by decide) cl22 (ClearPlan.cons (by decide) cl23 (ClearPlan.nil (st 5436)))))))))

private theorem abort_row2 : SerializedBody.machine.step (SerializedBodyRefinement.getAbort ⟨2,by decide⟩) none=((st 5684),none,.stay) := by rfl

private theorem fh0 : FromHRows (st 273) (st 337) := by
  exact ⟨(st 271),(st 272),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem dq0 : DecRows 6 (st 336) (st 270) (st 308) := by
  exact ⟨(st 324),(st 309),(st 323),(st 322),(st 296),(st 321),by decide,by decide,by decide,by decide,
    (RouteR.next (s:=(st 335)) (q:=(st 334)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 333)) (q:=(st 332)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 331)) (q:=(st 330)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 329)) (q:=(st 328)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 327)) (q:=(st 326)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 325)) (q:=(st 324)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 6 (st 324)))))))),
    (RouteL.next (s:=(st 295)) (q:=(st 294)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 293)) (q:=(st 292)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 291)) (q:=(st 290)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 289)) (q:=(st 288)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 287)) (q:=(st 286)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 285)) (q:=(st 270)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 270)))))))),
    (RouteL.next (s:=(st 320)) (q:=(st 319)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 318)) (q:=(st 317)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 316)) (q:=(st 315)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 314)) (q:=(st 313)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 312)) (q:=(st 311)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 310)) (q:=(st 308)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 308)))))))),rfl,rfl,(by
      intro b h
      cases b with
      | none => rfl
      | some b =>
        cases b with
        | false => rfl
        | true => exact False.elim (h rfl)),rfl,rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem entry0 : EntryRows ⟨0,by decide⟩ := by
  exact ⟨(st 273),(st 337),(st 336),(st 308),rfl,fh0,by decide,rfl,dq0⟩

private theorem fh1 : FromHRows (st 3310) (st 3362) := by
  exact ⟨(st 3308),(st 3309),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem dq1 : DecRows 6 (st 3361) (st 3307) (st 3333) := by
  exact ⟨(st 3349),(st 3334),(st 3348),(st 3347),(st 2352),(st 3346),by decide,by decide,by decide,by decide,
    (RouteR.next (s:=(st 3360)) (q:=(st 3359)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3358)) (q:=(st 3357)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3356)) (q:=(st 3355)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3354)) (q:=(st 3353)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3352)) (q:=(st 3351)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3350)) (q:=(st 3349)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 6 (st 3349)))))))),
    (RouteL.next (s:=(st 2351)) (q:=(st 2350)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2349)) (q:=(st 2348)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2347)) (q:=(st 2346)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2345)) (q:=(st 2344)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2343)) (q:=(st 2342)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2341)) (q:=(st 3307)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3307)))))))),
    (RouteL.next (s:=(st 3345)) (q:=(st 3344)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3343)) (q:=(st 3342)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3341)) (q:=(st 3340)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3339)) (q:=(st 3338)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3337)) (q:=(st 3336)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3335)) (q:=(st 3333)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3333)))))))),rfl,rfl,(by
      intro b h
      cases b with
      | none => rfl
      | some b =>
        cases b with
        | false => rfl
        | true => exact False.elim (h rfl)),rfl,rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem entry1 : EntryRows ⟨1,by decide⟩ := by
  exact ⟨(st 3310),(st 3362),(st 3361),(st 3333),rfl,fh1,by decide,rfl,dq1⟩

private theorem fh2 : FromHRows (st 5688) (st 5740) := by
  exact ⟨(st 5686),(st 5687),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem dq2 : DecRows 6 (st 5739) (st 5685) (st 5711) := by
  exact ⟨(st 5727),(st 5712),(st 5726),(st 5725),(st 2413),(st 5724),by decide,by decide,by decide,by decide,
    (RouteR.next (s:=(st 5738)) (q:=(st 5737)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5736)) (q:=(st 5735)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5734)) (q:=(st 5733)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5732)) (q:=(st 5731)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5730)) (q:=(st 5729)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5728)) (q:=(st 5727)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 6 (st 5727)))))))),
    (RouteL.next (s:=(st 2412)) (q:=(st 2411)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2410)) (q:=(st 2409)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2408)) (q:=(st 2407)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2406)) (q:=(st 2405)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2404)) (q:=(st 2403)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2402)) (q:=(st 5685)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5685)))))))),
    (RouteL.next (s:=(st 5723)) (q:=(st 5722)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5721)) (q:=(st 5720)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5719)) (q:=(st 5718)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5717)) (q:=(st 5716)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5715)) (q:=(st 5714)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5713)) (q:=(st 5711)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5711)))))))),rfl,rfl,(by
      intro b h
      cases b with
      | none => rfl
      | some b =>
        cases b with
        | false => rfl
        | true => exact False.elim (h rfl)),rfl,rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem entry2 : EntryRows ⟨2,by decide⟩ := by
  exact ⟨(st 5688),(st 5740),(st 5739),(st 5711),rfl,fh2,by decide,rfl,dq2⟩

private theorem in0 : IncRows 5 (st 308) (st 451) := by
  exact ⟨(st 298),(st 297),(st 284),(st 283),by decide,by decide,by decide,
    (RouteR.next (s:=(st 307)) (q:=(st 306)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 305)) (q:=(st 304)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 303)) (q:=(st 302)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 301)) (q:=(st 300)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 299)) (q:=(st 298)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 5 (st 298))))))),
    (RouteL.next (s:=(st 282)) (q:=(st 281)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 280)) (q:=(st 279)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 278)) (q:=(st 277)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 276)) (q:=(st 275)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 274)) (q:=(st 451)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 451))))))),rfl,rfl,rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem nd0 : NeedRows ⟨0,by decide⟩ := by
  exact ⟨(st 336),(st 308),(st 451),rfl,dq0,in0,by decide,rfl⟩

private theorem ed0 : EntryDirect ⟨0,by decide⟩ := by
  exact ⟨(st 273),rfl,fh0⟩

private theorem in1 : IncRows 5 (st 3333) (st 3468) := by
  exact ⟨(st 3323),(st 3322),(st 3321),(st 3320),by decide,by decide,by decide,
    (RouteR.next (s:=(st 3332)) (q:=(st 3331)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3330)) (q:=(st 3329)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3328)) (q:=(st 3327)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3326)) (q:=(st 3325)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3324)) (q:=(st 3323)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 5 (st 3323))))))),
    (RouteL.next (s:=(st 3319)) (q:=(st 3318)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3317)) (q:=(st 3316)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3315)) (q:=(st 3314)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3313)) (q:=(st 3312)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3311)) (q:=(st 3468)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3468))))))),rfl,rfl,rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem nd1 : NeedRows ⟨1,by decide⟩ := by
  exact ⟨(st 3361),(st 3333),(st 3468),rfl,dq1,in1,by decide,rfl⟩

private theorem ed1 : EntryDirect ⟨1,by decide⟩ := by
  exact ⟨(st 3310),rfl,fh1⟩

private theorem in2 : IncRows 5 (st 5711) (st 5812) := by
  exact ⟨(st 5701),(st 5700),(st 5699),(st 5698),by decide,by decide,by decide,
    (RouteR.next (s:=(st 5710)) (q:=(st 5709)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5708)) (q:=(st 5707)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5706)) (q:=(st 5705)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5704)) (q:=(st 5703)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 5702)) (q:=(st 5701)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 5 (st 5701))))))),
    (RouteL.next (s:=(st 5697)) (q:=(st 5696)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5695)) (q:=(st 5694)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5693)) (q:=(st 5692)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5691)) (q:=(st 5690)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 5689)) (q:=(st 5812)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 5812))))))),rfl,rfl,rfl,(by intro b;cases b <;> rfl),rfl⟩

private theorem nd2 : NeedRows ⟨2,by decide⟩ := by
  exact ⟨(st 5739),(st 5711),(st 5812),rfl,dq2,in2,by decide,rfl⟩

private theorem ed2 : EntryDirect ⟨2,by decide⟩ := by
  exact ⟨(st 5688),rfl,fh2⟩

end LiteralRows
private theorem physical_actual (b : Bool) : PhysicalAbort b := by
  cases b
  · exact ⟨st 269,st 21,abort_row0,plan0,rs0⟩
  · exact ⟨st 3306,st 3058,abort_row1,plan1,rs1⟩
private theorem virtual_actual : VirtualAbort := by
  exact ⟨st 5684,st 5436,abort_row2,plan2,toh2⟩
private theorem entries_actual (m : Fin 3) : EntryRows m := by
  fin_cases m
  · exact entry0
  · exact entry1
  · exact entry2
private theorem direct_actual (m : Fin 3) : EntryDirect m := by
  fin_cases m
  · exact ed0
  · exact ed1
  · exact ed2
private theorem needs_actual (m : Fin 3) : NeedRows m := by
  fin_cases m
  · exact nd0
  · exact nd1
  · exact nd2
theorem abort_cleanup (D : Nat → Nat) (T : Nat → Option Bool) (S L H Q F c N B P : Nat)
    (source : Fin S → Bool) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) (hH : H < tapeLength N B)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let clearedTape : Nat → Option Bool:=fun i=>if D 10 < i ∧ i < D 11 then some true else
      if [1,4,5,6,8,9,11].any (fun j=>decide (D j < i ∧ i < D (j+1))) then some false else T i
    let initial : Config 7500 N B:=⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source c),⟨D 0,h0⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 512*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else clearedTape i.val else clearedTape i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  exact cleanup_result physical_actual virtual_actual D T S L H Q F c N B P source ⟨rise,mono,blank,cells⟩ sl lh positive arena anchor room fit h0 hH ts tl th tf reg ass marks gap hole src

theorem zero_quota_native (D : Nat → Nat) (T : Nat → Option Bool) (S L H Q F c N B P : Nat)
    (source : Fin S → Bool) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (hH : H < tapeLength N B)
    (quota : ∀ i,D 6 < i → i < D 7 → T i=some false)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let clearedTape : Nat → Option Bool:=fun i=>if D 10 < i ∧ i < D 11 then some true else
      if [1,4,5,6,8,9,11].any (fun j=>decide (D j < i ∧ i < D (j+1))) then some false else T i
    let initial : Config 7500 N B:=⟨SerializedBody.entry (SerializedBody.sourceMode source c),⟨H,hH⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 1024*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else clearedTape i.val else clearedTape i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  exact zero_result physical_actual virtual_actual entries_actual D T S L H Q F c N B P source ⟨rise,mono,blank,cells⟩ sl lh positive arena anchor room fit hH quota ts tl th tf reg ass marks gap hole src

theorem entry_need (mode : Fin 3) (T : Nat → Option Bool) (H Q F N B P : Nat)
    (positive : 0 < Q) (arena : H+Q < F) (room : F+1 ≤ P) (fit : P < tapeLength N B)
    (hH : H < tapeLength N B) (h0 : F+1 < tapeLength N B) (th : T H=none) (tf : T F=some false)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none) :
    let initial : Config 7500 N B:=⟨SerializedBody.entry mode,⟨H,hH⟩,fun i=>T i.val⟩
    SerializedBody.machine.run (F+2-H) initial=⟨needEntry mode,⟨F+1,h0⟩,fun i=>T i.val⟩ ∧
      ∀ u,u ≤ F+2-H → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  exact entry_result direct_actual mode T H Q F N B P positive arena room fit hH h0 th tf marks gap

theorem need_get (mode : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool) (r q v N B P : Nat)
    (rise : ∀ j,j < 12 → D j < D (j+1)) (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B)
    (positive : 0 < q) (bound : q+v ≤ r) (len5 : D 6=D 5+r+1) (len6 : D 7=D 6+r+1)
    (quota : ∀ i,D 6 < i → i < D 7 → T i=some (decide (i-D 6 ≤ q)))
    (nodes : ∀ i,D 5 < i → i < D 6 → T i=some (decide (i-D 5 ≤ v))) :
    let ticks:=1+(2*(D 6-D 0+6)+2*q+4)+(2*(D 5-D 0+5)+2*v+4)+1
    let initial : Config 7500 N B:=⟨needEntry mode,⟨D 0,h0⟩,fun i=>T i.val⟩
    ticks ≤ 128*(P+1) ∧ SerializedBody.machine.run ticks initial=
      ⟨SerializedBodyRefinement.getEntry ⟨0,by decide⟩ mode,⟨D 0,h0⟩,
        fun i=>if i.val=D 5+v+1 then some true else if i.val=D 6+q then some false else T i.val⟩ ∧
      ∀ u,u ≤ ticks → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  exact need_result needs_actual mode D T r q v N B P ⟨rise,mono,blank,cells⟩ room fit h0 positive bound len5 len6 quota nodes
#print axioms SerializedBodyCompletion.abort_cleanup
#print axioms SerializedBodyCompletion.zero_quota_native
#print axioms SerializedBodyCompletion.entry_need
#print axioms SerializedBodyCompletion.need_get
end SerializedBodyCompletion
