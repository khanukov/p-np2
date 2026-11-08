import SerializedBodyRefinement.Proof
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
private def bm (b : Bool) : Fin 3 := ⟨if b then 1 else 0,by cases b <;> decide⟩
private def sourcePatch (T : Nat → Option Bool) (c : Nat) (b : Bool) :=
  put (put T c (some b)) (c+1) none
private def SourceRows (b : Bool) (entry : Fin 7500) (out : Fin 3 → Fin 7500) : Prop :=
  ∃ seek lift : Fin 7500, ∃ back : Bool → Fin 7500,
    4 ≤ entry.val ∧ 4 ≤ seek.val ∧ 4 ≤ lift.val ∧ (∀ v,4 ≤ (back v).val) ∧
    SerializedBody.machine.step entry none=(seek,none,.left) ∧
    (∀ v,SerializedBody.machine.step seek (some v)=(seek,some v,.left)) ∧
    SerializedBody.machine.step seek none=(lift,some b,.right) ∧
    SerializedBody.machine.step lift none=(out ⟨2,by decide⟩,none,.stay) ∧
    (∀ v,SerializedBody.machine.step lift (some v)=(back v,none,.right)) ∧
    (∀ v w,SerializedBody.machine.step (back v) (some w)=(back v,some w,.right)) ∧
    (∀ v,SerializedBody.machine.step (back v) none=(out (bm v),none,.stay))
private theorem source_step {S c P T b entry out} (source : Fin S → Bool)
    (physical : c < S) (fit : S ≤ P) (eof : T S=none) (hole : T c=none)
    (cells : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (rows : SourceRows b entry out) :
    Path P (2*(S-c)+1) ⟨entry,S,T⟩
      ⟨out (SerializedBody.sourceMode source (c+1)),S,sourcePatch T c b⟩ := by
  rcases rows with ⟨seek,lift,back,se,ss,sl,sb,re,rs,rl,rn,rb,rr,rf⟩
  have one:=keep entry seek S (S-1) T .left (P:=P) fit (by omega) se (by rw [eof]; exact re) rfl
  have seekpath:=sweepL seek T c (S-1-c) (P:=P) (by omega) ss (by
    intro i lo hi
    rw [cells i lo (by omega)]
    exact rs _)
  rw [show c+(S-1-c)=S-1 by omega] at seekpath
  let U:=put T c (some b)
  have restore:=hop seek lift c (c+1) T (some b) .right (P:=P) (by omega) (by omega) ss (by rw [hole]; exact rl) rfl
  by_cases next : c+1 < S
  · let v:=source ⟨c+1,next⟩
    have read : U (c+1)=some v := by
      simp only [U,put,if_neg (by omega : c+1≠c)]
      exact cells _ (by omega) next
    let V:=put U (c+1) none
    have take:=hop lift (back v) (c+1) (c+2) U none .right (P:=P) (by omega) (by omega) sl (by rw [read]; exact rb v) (by simp [dest])
    have returnpath:=sweepR (back v) V (c+2) (S-(c+2)) (P:=P) (by omega) (sb v) (by
      intro i lo hi
      have old : V i=T i := by
        simp only [V,U,put,if_neg (by omega : i≠c+1),if_neg (by omega : i≠c)]
      rw [old,cells i (by omega) (by omega)]
      exact rr v _)
    rw [show c+2+(S-(c+2))=S by omega] at returnpath
    have endblank : V S=none := by
      simp only [V,U,put,if_neg (by omega : S≠c+1),if_neg (by omega : S≠c)]
      exact eof
    have last:=keep (back v) (out (bm v)) S S V .stay (P:=P) fit fit (sb v) (by rw [endblank]; exact rf v) rfl
    have mode : SerializedBody.sourceMode source (c+1)=bm v := by
      simp only [SerializedBody.sourceMode,dif_pos next]
      cases hv : source ⟨c+1,next⟩ <;> simp [bm,v,hv]
    rw [mode]
    have whole:=one.append (seekpath.append (restore.append (take.append (returnpath.append last))))
    convert whole using 1
    omega
  · have eq : c+1=S := by omega
    have mode : SerializedBody.sourceMode source (c+1)=⟨2,by decide⟩ := by
      simp only [SerializedBody.sourceMode,dif_neg next]
    have endblank : U (c+1)=none := by
      simp only [U,put,if_neg (by omega : c+1≠c)]
      rw [eq]; exact eof
    have last:=keep lift (out ⟨2,by decide⟩) (c+1) (c+1) U .stay (P:=P) (by omega) (by omega) sl (by rw [endblank]; exact rn) rfl
    rw [eq] at restore last
    have cleared : sourcePatch T c b=U := by
      change put U (c+1) none=U
      rw [← endblank,put_same]
    rw [mode,cleared]
    have whole:=one.append (seekpath.append (restore.append last))
    convert whole using 1
    omega
private theorem sourcePatch_above {T c S b i} (hc : c < S) (hi : S < i) :
    sourcePatch T c b i=T i := by
  simp only [sourcePatch,put,if_neg (by omega : i≠c+1),if_neg (by omega : i≠c)]
private theorem sourcePatch_eof {T c S b} (hc : c < S) (old : T S=none) :
    sourcePatch T c b S=none := by
  by_cases eq : S=c+1
  · simp only [sourcePatch,put,if_pos eq]
  · simp only [sourcePatch,put,if_neg eq,if_neg (by omega : S≠c)]; exact old
private def PhysicalRows (b : Bool) (entry : Fin 7500) (out : Fin 3 → Fin 7500) : Prop :=
  ∃ h s : Fin 7500, ∃ afterS afterH : Fin 3 → Fin 7500,
    ToHRows entry h ∧ RouteL 2 0 h s ∧ SourceRows b s afterS ∧
    (∀ m,RouteR 0 2 (afterS m) (afterH m)) ∧
    (∀ m,FromHRows (afterH m) (out m))
private theorem physical_get {S L H Q F P c T b entry out} (source : Fin S → Bool)
    (sl : S < L) (lh : L < H) (positive : 0 < Q) (room : H+Q < F)
    (fit : F+1 ≤ P) (physical : c < S) (hole : T c=none)
    (eof : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false) (td : T (F+1)=none)
    (sourceCells : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (code : PhysicalRows b entry out) :
    Path P (2*(F-c)+8) ⟨entry,F+1,T⟩
      ⟨out (SerializedBody.sourceMode source (c+1)),F+1,sourcePatch T c b⟩ := by
  rcases code with ⟨h,s,asS,asH,rowsH,rowsL,rowsS,rowsR,rowsF⟩
  have first:=to_H positive room fit td tf th marks gap rowsH
  have second:=header_left (P:=P) sl lh (by omega) eof tl th reg ass rowsL
  have third:=source_step (P:=P) source physical (by omega) eof hole sourceCells rowsS
  let U:=sourcePatch T c b
  have old (i : Nat) (hi : S < i) : U i=T i := sourcePatch_above physical hi
  have eof' : U S=none := sourcePatch_eof physical eof
  have tl' : U L=none := by rw [old L sl]; exact tl
  have th' : U H=none := by rw [old H (by omega)]; exact th
  have fourth:=header_right (P:=P) sl lh (by omega) eof' tl' th'
    (by intro i lo hi; rw [old i lo]; exact reg i lo hi)
    (by intro i lo hi; rw [old i (by omega)]; exact ass i lo hi)
    (rowsR (SerializedBody.sourceMode source (c+1)))
  have fifth:=from_H positive room fit (T:=U)
    (by rw [old F (by omega)]; exact tf) th'
    (by intro i lo hi; rw [old i (by omega)]; exact marks i lo hi)
    (by intro i lo hi; rw [old i (by omega)]; exact gap i lo hi)
    (rowsF (SerializedBody.sourceMode source (c+1)))
  have whole:=first.append (second.append (third.append (fourth.append fifth)))
  convert whole using 1
  omega


def getExit (site : Fin 9) (bit : Bool) (mode : Fin 3) : Fin 7500 :=
  st (#[553,3570,5880,655,3672,5948,757,3774,6016,1108,3876,6084,1303,3955,6152,1405,4034,6198,2226,4842,6943,1507,4133,6266,809,861,913,944,975,1006,1139,1170,1201,270,3307,5685,270,3307,5685,270,3307,5685,1884,4505,6612,2218,4834,6935,2340,2401,2462,2484,2506,2528][6*site.val+3*(if bit then 1 else 0)+mode.val]!)
private def pin_getExit : Fin 9 → Bool → Fin 3 → Fin 7500 := getExit
#print axioms SerializedBodyRefinement.getExit
#print axioms pin_getExit

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
private theorem join_safe {N B : Nat} (a b : Nat) (c d e : Config 7500 N B)
    (first : SerializedBody.machine.run a c=d) (second : SerializedBody.machine.run b d=e)
    (safeA : ∀ u,u ≤ a → 4 ≤ (SerializedBody.machine.run u c).state.val)
    (safeB : ∀ u,u ≤ b → 4 ≤ (SerializedBody.machine.run u d).state.val) :
    SerializedBody.machine.run (a+b) c=e ∧ ∀ u,u ≤ a+b → 4 ≤ (SerializedBody.machine.run u c).state.val := by
  constructor
  · rw [SerializedBody.machine.run_add,first,second]
  · intro u hu
    by_cases before : u ≤ a
    · exact safeA u before
    · have split : u=a+(u-a) := by omega
      rw [split,SerializedBody.machine.run_add,first]
      exact safeB _ (by omega)
private theorem reader_price (d0 d4 d11 r v u F c P : Nat)
    (h4 : d4 ≤ P) (h11 : d11 ≤ P) (hr : r ≤ P) (hv : v+u ≤ r) (hf : F ≤ P) :
    (if v=0 then 2*(d4-d0+4)+3 else 2*(d4-d0+4)+2*(d11-d0+11)+2*v+2*u+8+2*(F-c)+8) ≤ 64*(P+1) := by
  have a:=Nat.sub_le d4 d0
  have b:=Nat.sub_le d11 d0
  have e:=Nat.sub_le F c
  split_ifs <;> omega
/-- Complete actual Get routine, for every call-site and physical/virtual source.
Empty remaining goes to the existing LIVE abort entry, not yet literal reject.
This is a prepared internal consumer, not full Body/RAW/evaluator correctness. -/
private theorem reader_core
    (physical_code : ∀ site bit,PhysicalRows bit (getBody site (bm bit)) (fun m => getExit site bit m))
    (body_virtual : ∀ site,getBody site ⟨2,by decide⟩=getExit site false ⟨2,by decide⟩)
    (exits_safe : ∀ site bit mode,4 ≤ (getExit site bit mode).val)
    (site : Fin 9) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r v u c N B P : Nat) (source : Fin S → Bool)
    (hv : v+u ≤ r) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (remaining : ∀ i,D 4 < i → i < D 5 → T i=some (decide (i-D 4 ≤ v)))
    (consumed : ∀ i,D 11 < i → i < D 12 → T i=some (decide (i-D 11 ≤ u)))
    (eof : T S=none) (left : T L=none) (right : T H=none) (fence : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none)
    (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let C : Nat → Option Bool:=fun i => if i=D 11+u+1 then some true else if i=D 4+v then some false else T i
    let initial : Config 7500 N B:=⟨getEntry site (SerializedBody.sourceMode source c),⟨D 0,h0⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 64*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨(if v=0 then getAbort (SerializedBody.sourceMode source c) else
          getExit site (Pnp4.Frontier.ContractExpansion.padRead source c) (SerializedBody.sourceMode source (c+1))),
        ⟨D 0,h0⟩,fun i=>if v=0 then T i.val else if c < S then
          if i.val=c+1 then none else if i.val=c then some (Pnp4.Frontier.ContractExpansion.padRead source c) else C i.val
          else C i.val⟩ ∧ ∀ j,j ≤ t → 4 ≤ (SerializedBody.machine.run j initial).state.val := by
  dsimp only
  let C : Nat → Option Bool:=fun i => if i=D 11+u+1 then some true else if i=D 4+v then some false else T i
  have counter:=counter_phase site (SerializedBody.sourceMode source c) D T r v u N B P hv rise mono blank cells len4 len11 remaining consumed room fit h0
  dsimp only at counter
  have d4 : D 4 ≤ P:=le_trans (mono 4 12 (by decide) le_rfl) room
  have d11 : D 11 ≤ P:=le_trans (mono 11 12 (by decide) le_rfl) room
  have d0 : D 0 ≤ P:=le_trans (mono 0 12 (by decide) le_rfl) room
  have dr : r ≤ P := by have d5:=le_trans (mono 5 12 (by decide) le_rfl) room; omega
  have ff : F+1 ≤ P := by omega
  have bound:=reader_price (D 0) (D 4) (D 11) r v u F c P d4 d11 dr hv (by omega)
  by_cases zero : v=0
  · subst v
    simp only [↓reduceIte] at counter bound ⊢
    exact ⟨2*(D 4-D 0+4)+3,bound,counter.1,counter.2⟩
  · simp only [if_neg zero] at counter bound ⊢
    let ticks:=2*(D 4-D 0+4)+2*(D 11-D 0+11)+2*v+2*u+8
    have below (i : Nat) (hi : i ≤ F+1) : C i=T i := by
      have p4:=mono 0 4 (by decide) (by decide)
      have p11:=mono 0 11 (by decide) (by decide)
      simp only [C,if_neg (by omega : i≠D 11+u+1),if_neg (by omega : i≠D 4+v)]
    by_cases physical : c < S
    · have oldMode : SerializedBody.sourceMode source c=bm (Pnp4.Frontier.ContractExpansion.padRead source c) := by
        rw [Pnp4.Frontier.ContractExpansion.padRead_lt source physical]
        simp only [SerializedBody.sourceMode,dif_pos physical]
        cases hb : source ⟨c,physical⟩ <;> simp [bm]
      have path:=physical_get (P:=P) source sl lh positive arena ff physical (T:=C)
        (by rw [below c (by omega)]; exact hole physical)
        (by rw [below S (by omega)]; exact eof)
        (by rw [below L (by omega)]; exact left)
        (by rw [below H (by omega)]; exact right)
        (by rw [below F (by omega)]; exact fence)
        (by rw [← anchor,below (D 0) (by omega)]; exact blank 0 (by decide))
        (by intro i lo hi; rw [below i (by omega)]; exact src i lo hi)
        (by intro i lo hi; rw [below i (by omega)]; exact reg i lo hi)
        (by intro i lo hi; rw [below i (by omega)]; exact ass i lo hi)
        (by intro i lo hi; rw [below i (by omega)]; exact marks i lo hi)
        (by intro i lo hi; rw [below i (by omega)]; exact gap i lo hi)
        (physical_code site (Pnp4.Frontier.ContractExpansion.padRead source c))
      rw [← anchor,← oldMode] at path
      have final:=path.execute fit
      have safe:=path.through fit (exits_safe site _ _)
      dsimp only [embed] at final safe
      have joined:=join_safe ticks (2*(F-c)+8) _ _ _ counter.1 final counter.2 safe
      refine ⟨ticks+(2*(F-c)+8),by dsimp only [ticks]; omega,?_,joined.2⟩
      simpa only [sourcePatch,put,if_pos physical] using joined.1
    · have current : SerializedBody.sourceMode source c=⟨2,by decide⟩ := by simp only [SerializedBody.sourceMode,dif_neg physical]
      have next : SerializedBody.sourceMode source (c+1)=⟨2,by decide⟩ := by
        simp only [SerializedBody.sourceMode,dif_neg (by omega : ¬c+1 < S)]
      have read : Pnp4.Frontier.ContractExpansion.padRead source c=false :=
        Pnp4.Frontier.ContractExpansion.padRead_ge source (by omega)
      refine ⟨ticks,by dsimp only [ticks]; omega,?_,counter.2⟩
      simpa only [current,body_virtual,next,read,if_neg physical] using counter.1
section BackendRows
set_option maxRecDepth 4000
private theorem to0 : ToHRows (st 371) (st 367) := by
  exact ⟨(st 370),(st 369),(st 368),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute0 : RouteL 2 0 (st 367) (st 363) :=
  (RouteL.next (s:=(st 364)) (q:=(st 366)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 365)) (q:=(st 363)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 363))))
private theorem src0 : SourceRows false (st 363) (fun m : Fin 3 => st (#[351,359,344][m.val]!)) := by
  exact ⟨(st 362),(st 361),(fun b : Bool => if b then (st 360) else (st 352)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute1 : RouteR 0 2 (st 351) (st 347) :=
  (RouteR.next (s:=(st 349)) (q:=(st 350)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 348)) (q:=(st 347)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 347))))
private theorem broute2 : RouteR 0 2 (st 359) (st 355) :=
  (RouteR.next (s:=(st 357)) (q:=(st 358)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 356)) (q:=(st 355)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 355))))
private theorem broute3 : RouteR 0 2 (st 344) (st 340) :=
  (RouteR.next (s:=(st 342)) (q:=(st 343)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 341)) (q:=(st 340)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 340))))
private theorem from0 : FromHRows (st 347) (st 553) := by
  exact ⟨(st 345),(st 346),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from1 : FromHRows (st 355) (st 3570) := by
  exact ⟨(st 353),(st 354),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from2 : FromHRows (st 340) (st 5880) := by
  exact ⟨(st 338),(st 339),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph0 : PhysicalRows false (st 371) (fun m => getExit ⟨0,by decide⟩ false m) := by
  refine ⟨(st 367),(st 363),(fun m : Fin 3 => st (#[351,359,344][m.val]!)),(fun m : Fin 3 => st (#[347,355,340][m.val]!)),to0,broute0,src0,?_,?_⟩
  · intro m; fin_cases m
    · exact broute1
    · exact broute2
    · exact broute3
  · intro m; fin_cases m
    · exact from0
    · exact from1
    · exact from2
private theorem to1 : ToHRows (st 485) (st 481) := by
  exact ⟨(st 484),(st 483),(st 482),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute4 : RouteL 2 0 (st 481) (st 477) :=
  (RouteL.next (s:=(st 478)) (q:=(st 480)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 479)) (q:=(st 477)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 477))))
private theorem src1 : SourceRows false (st 477) (fun m : Fin 3 => st (#[465,473,458][m.val]!)) := by
  exact ⟨(st 476),(st 475),(fun b : Bool => if b then (st 474) else (st 466)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute5 : RouteR 0 2 (st 465) (st 461) :=
  (RouteR.next (s:=(st 463)) (q:=(st 464)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 462)) (q:=(st 461)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 461))))
private theorem broute6 : RouteR 0 2 (st 473) (st 469) :=
  (RouteR.next (s:=(st 471)) (q:=(st 472)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 470)) (q:=(st 469)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 469))))
private theorem broute7 : RouteR 0 2 (st 458) (st 454) :=
  (RouteR.next (s:=(st 456)) (q:=(st 457)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 455)) (q:=(st 454)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 454))))
private theorem from3 : FromHRows (st 461) (st 757) := by
  exact ⟨(st 459),(st 460),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from4 : FromHRows (st 469) (st 3774) := by
  exact ⟨(st 467),(st 468),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from5 : FromHRows (st 454) (st 6016) := by
  exact ⟨(st 452),(st 453),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph1 : PhysicalRows false (st 485) (fun m => getExit ⟨1,by decide⟩ false m) := by
  refine ⟨(st 481),(st 477),(fun m : Fin 3 => st (#[465,473,458][m.val]!)),(fun m : Fin 3 => st (#[461,469,454][m.val]!)),to1,broute4,src1,?_,?_⟩
  · intro m; fin_cases m
    · exact broute5
    · exact broute6
    · exact broute7
  · intro m; fin_cases m
    · exact from3
    · exact from4
    · exact from5
private theorem to2 : ToHRows (st 587) (st 583) := by
  exact ⟨(st 586),(st 585),(st 584),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute8 : RouteL 2 0 (st 583) (st 579) :=
  (RouteL.next (s:=(st 580)) (q:=(st 582)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 581)) (q:=(st 579)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 579))))
private theorem src2 : SourceRows false (st 579) (fun m : Fin 3 => st (#[567,575,560][m.val]!)) := by
  exact ⟨(st 578),(st 577),(fun b : Bool => if b then (st 576) else (st 568)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute9 : RouteR 0 2 (st 567) (st 563) :=
  (RouteR.next (s:=(st 565)) (q:=(st 566)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 564)) (q:=(st 563)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 563))))
private theorem broute10 : RouteR 0 2 (st 575) (st 571) :=
  (RouteR.next (s:=(st 573)) (q:=(st 574)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 572)) (q:=(st 571)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 571))))
private theorem broute11 : RouteR 0 2 (st 560) (st 556) :=
  (RouteR.next (s:=(st 558)) (q:=(st 559)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 557)) (q:=(st 556)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 556))))
private theorem from6 : FromHRows (st 563) (st 1303) := by
  exact ⟨(st 561),(st 562),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from7 : FromHRows (st 571) (st 3955) := by
  exact ⟨(st 569),(st 570),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from8 : FromHRows (st 556) (st 6152) := by
  exact ⟨(st 554),(st 555),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph2 : PhysicalRows false (st 587) (fun m => getExit ⟨2,by decide⟩ false m) := by
  refine ⟨(st 583),(st 579),(fun m : Fin 3 => st (#[567,575,560][m.val]!)),(fun m : Fin 3 => st (#[563,571,556][m.val]!)),to2,broute8,src2,?_,?_⟩
  · intro m; fin_cases m
    · exact broute9
    · exact broute10
    · exact broute11
  · intro m; fin_cases m
    · exact from6
    · exact from7
    · exact from8
private theorem to3 : ToHRows (st 689) (st 685) := by
  exact ⟨(st 688),(st 687),(st 686),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute12 : RouteL 2 0 (st 685) (st 681) :=
  (RouteL.next (s:=(st 682)) (q:=(st 684)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 683)) (q:=(st 681)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 681))))
private theorem src3 : SourceRows false (st 681) (fun m : Fin 3 => st (#[669,677,662][m.val]!)) := by
  exact ⟨(st 680),(st 679),(fun b : Bool => if b then (st 678) else (st 670)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute13 : RouteR 0 2 (st 669) (st 665) :=
  (RouteR.next (s:=(st 667)) (q:=(st 668)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 666)) (q:=(st 665)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 665))))
private theorem broute14 : RouteR 0 2 (st 677) (st 673) :=
  (RouteR.next (s:=(st 675)) (q:=(st 676)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 674)) (q:=(st 673)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 673))))
private theorem broute15 : RouteR 0 2 (st 662) (st 658) :=
  (RouteR.next (s:=(st 660)) (q:=(st 661)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 659)) (q:=(st 658)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 658))))
private theorem from9 : FromHRows (st 665) (st 2226) := by
  exact ⟨(st 663),(st 664),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from10 : FromHRows (st 673) (st 4842) := by
  exact ⟨(st 671),(st 672),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from11 : FromHRows (st 658) (st 6943) := by
  exact ⟨(st 656),(st 657),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph3 : PhysicalRows false (st 689) (fun m => getExit ⟨3,by decide⟩ false m) := by
  refine ⟨(st 685),(st 681),(fun m : Fin 3 => st (#[669,677,662][m.val]!)),(fun m : Fin 3 => st (#[665,673,658][m.val]!)),to3,broute12,src3,?_,?_⟩
  · intro m; fin_cases m
    · exact broute13
    · exact broute14
    · exact broute15
  · intro m; fin_cases m
    · exact from9
    · exact from10
    · exact from11
private theorem to4 : ToHRows (st 1040) (st 1036) := by
  exact ⟨(st 1039),(st 1038),(st 1037),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute16 : RouteL 2 0 (st 1036) (st 1032) :=
  (RouteL.next (s:=(st 1033)) (q:=(st 1035)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1034)) (q:=(st 1032)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1032))))
private theorem src4 : SourceRows false (st 1032) (fun m : Fin 3 => st (#[1020,1028,1013][m.val]!)) := by
  exact ⟨(st 1031),(st 1030),(fun b : Bool => if b then (st 1029) else (st 1021)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute17 : RouteR 0 2 (st 1020) (st 1016) :=
  (RouteR.next (s:=(st 1018)) (q:=(st 1019)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1017)) (q:=(st 1016)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1016))))
private theorem broute18 : RouteR 0 2 (st 1028) (st 1024) :=
  (RouteR.next (s:=(st 1026)) (q:=(st 1027)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1025)) (q:=(st 1024)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1024))))
private theorem broute19 : RouteR 0 2 (st 1013) (st 1009) :=
  (RouteR.next (s:=(st 1011)) (q:=(st 1012)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1010)) (q:=(st 1009)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1009))))
private theorem from12 : FromHRows (st 1016) (st 809) := by
  exact ⟨(st 1014),(st 1015),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from13 : FromHRows (st 1024) (st 861) := by
  exact ⟨(st 1022),(st 1023),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from14 : FromHRows (st 1009) (st 913) := by
  exact ⟨(st 1007),(st 1008),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph4 : PhysicalRows false (st 1040) (fun m => getExit ⟨4,by decide⟩ false m) := by
  refine ⟨(st 1036),(st 1032),(fun m : Fin 3 => st (#[1020,1028,1013][m.val]!)),(fun m : Fin 3 => st (#[1016,1024,1009][m.val]!)),to4,broute16,src4,?_,?_⟩
  · intro m; fin_cases m
    · exact broute17
    · exact broute18
    · exact broute19
  · intro m; fin_cases m
    · exact from12
    · exact from13
    · exact from14
private theorem to5 : ToHRows (st 1235) (st 1231) := by
  exact ⟨(st 1234),(st 1233),(st 1232),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute20 : RouteL 2 0 (st 1231) (st 1227) :=
  (RouteL.next (s:=(st 1228)) (q:=(st 1230)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1229)) (q:=(st 1227)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1227))))
private theorem src5 : SourceRows false (st 1227) (fun m : Fin 3 => st (#[1215,1223,1208][m.val]!)) := by
  exact ⟨(st 1226),(st 1225),(fun b : Bool => if b then (st 1224) else (st 1216)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute21 : RouteR 0 2 (st 1215) (st 1211) :=
  (RouteR.next (s:=(st 1213)) (q:=(st 1214)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1212)) (q:=(st 1211)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1211))))
private theorem broute22 : RouteR 0 2 (st 1223) (st 1219) :=
  (RouteR.next (s:=(st 1221)) (q:=(st 1222)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1220)) (q:=(st 1219)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1219))))
private theorem broute23 : RouteR 0 2 (st 1208) (st 1204) :=
  (RouteR.next (s:=(st 1206)) (q:=(st 1207)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1205)) (q:=(st 1204)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1204))))
private theorem from15 : FromHRows (st 1211) (st 1139) := by
  exact ⟨(st 1209),(st 1210),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from16 : FromHRows (st 1219) (st 1170) := by
  exact ⟨(st 1217),(st 1218),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from17 : FromHRows (st 1204) (st 1201) := by
  exact ⟨(st 1202),(st 1203),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph5 : PhysicalRows false (st 1235) (fun m => getExit ⟨5,by decide⟩ false m) := by
  refine ⟨(st 1231),(st 1227),(fun m : Fin 3 => st (#[1215,1223,1208][m.val]!)),(fun m : Fin 3 => st (#[1211,1219,1204][m.val]!)),to5,broute20,src5,?_,?_⟩
  · intro m; fin_cases m
    · exact broute21
    · exact broute22
    · exact broute23
  · intro m; fin_cases m
    · exact from15
    · exact from16
    · exact from17
private theorem to6 : ToHRows (st 1337) (st 1333) := by
  exact ⟨(st 1336),(st 1335),(st 1334),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute24 : RouteL 2 0 (st 1333) (st 1329) :=
  (RouteL.next (s:=(st 1330)) (q:=(st 1332)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1331)) (q:=(st 1329)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1329))))
private theorem src6 : SourceRows false (st 1329) (fun m : Fin 3 => st (#[1317,1325,1310][m.val]!)) := by
  exact ⟨(st 1328),(st 1327),(fun b : Bool => if b then (st 1326) else (st 1318)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute25 : RouteR 0 2 (st 1317) (st 1313) :=
  (RouteR.next (s:=(st 1315)) (q:=(st 1316)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1314)) (q:=(st 1313)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1313))))
private theorem broute26 : RouteR 0 2 (st 1325) (st 1321) :=
  (RouteR.next (s:=(st 1323)) (q:=(st 1324)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1322)) (q:=(st 1321)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1321))))
private theorem broute27 : RouteR 0 2 (st 1310) (st 1306) :=
  (RouteR.next (s:=(st 1308)) (q:=(st 1309)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1307)) (q:=(st 1306)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1306))))
private theorem from18 : FromHRows (st 1313) (st 270) := by
  exact ⟨(st 1311),(st 1312),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from19 : FromHRows (st 1321) (st 3307) := by
  exact ⟨(st 1319),(st 1320),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from20 : FromHRows (st 1306) (st 5685) := by
  exact ⟨(st 1304),(st 1305),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph6 : PhysicalRows false (st 1337) (fun m => getExit ⟨6,by decide⟩ false m) := by
  refine ⟨(st 1333),(st 1329),(fun m : Fin 3 => st (#[1317,1325,1310][m.val]!)),(fun m : Fin 3 => st (#[1313,1321,1306][m.val]!)),to6,broute24,src6,?_,?_⟩
  · intro m; fin_cases m
    · exact broute25
    · exact broute26
    · exact broute27
  · intro m; fin_cases m
    · exact from18
    · exact from19
    · exact from20
private theorem to7 : ToHRows (st 1439) (st 1435) := by
  exact ⟨(st 1438),(st 1437),(st 1436),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute28 : RouteL 2 0 (st 1435) (st 1431) :=
  (RouteL.next (s:=(st 1432)) (q:=(st 1434)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 1433)) (q:=(st 1431)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 1431))))
private theorem src7 : SourceRows false (st 1431) (fun m : Fin 3 => st (#[1419,1427,1412][m.val]!)) := by
  exact ⟨(st 1430),(st 1429),(fun b : Bool => if b then (st 1428) else (st 1420)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute29 : RouteR 0 2 (st 1419) (st 1415) :=
  (RouteR.next (s:=(st 1417)) (q:=(st 1418)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1416)) (q:=(st 1415)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1415))))
private theorem broute30 : RouteR 0 2 (st 1427) (st 1423) :=
  (RouteR.next (s:=(st 1425)) (q:=(st 1426)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1424)) (q:=(st 1423)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1423))))
private theorem broute31 : RouteR 0 2 (st 1412) (st 1408) :=
  (RouteR.next (s:=(st 1410)) (q:=(st 1411)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 1409)) (q:=(st 1408)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 1408))))
private theorem from21 : FromHRows (st 1415) (st 1884) := by
  exact ⟨(st 1413),(st 1414),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from22 : FromHRows (st 1423) (st 4505) := by
  exact ⟨(st 1421),(st 1422),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from23 : FromHRows (st 1408) (st 6612) := by
  exact ⟨(st 1406),(st 1407),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph7 : PhysicalRows false (st 1439) (fun m => getExit ⟨7,by decide⟩ false m) := by
  refine ⟨(st 1435),(st 1431),(fun m : Fin 3 => st (#[1419,1427,1412][m.val]!)),(fun m : Fin 3 => st (#[1415,1423,1408][m.val]!)),to7,broute28,src7,?_,?_⟩
  · intro m; fin_cases m
    · exact broute29
    · exact broute30
    · exact broute31
  · intro m; fin_cases m
    · exact from21
    · exact from22
    · exact from23
private theorem to8 : ToHRows (st 2562) (st 2558) := by
  exact ⟨(st 2561),(st 2560),(st 2559),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute32 : RouteL 2 0 (st 2558) (st 2554) :=
  (RouteL.next (s:=(st 2555)) (q:=(st 2557)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 2556)) (q:=(st 2554)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 2554))))
private theorem src8 : SourceRows false (st 2554) (fun m : Fin 3 => st (#[2542,2550,2535][m.val]!)) := by
  exact ⟨(st 2553),(st 2552),(fun b : Bool => if b then (st 2551) else (st 2543)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute33 : RouteR 0 2 (st 2542) (st 2538) :=
  (RouteR.next (s:=(st 2540)) (q:=(st 2541)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2539)) (q:=(st 2538)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 2538))))
private theorem broute34 : RouteR 0 2 (st 2550) (st 2546) :=
  (RouteR.next (s:=(st 2548)) (q:=(st 2549)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2547)) (q:=(st 2546)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 2546))))
private theorem broute35 : RouteR 0 2 (st 2535) (st 2531) :=
  (RouteR.next (s:=(st 2533)) (q:=(st 2534)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 2532)) (q:=(st 2531)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 2531))))
private theorem from24 : FromHRows (st 2538) (st 2340) := by
  exact ⟨(st 2536),(st 2537),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from25 : FromHRows (st 2546) (st 2401) := by
  exact ⟨(st 2544),(st 2545),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from26 : FromHRows (st 2531) (st 2462) := by
  exact ⟨(st 2529),(st 2530),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph8 : PhysicalRows false (st 2562) (fun m => getExit ⟨8,by decide⟩ false m) := by
  refine ⟨(st 2558),(st 2554),(fun m : Fin 3 => st (#[2542,2550,2535][m.val]!)),(fun m : Fin 3 => st (#[2538,2546,2531][m.val]!)),to8,broute32,src8,?_,?_⟩
  · intro m; fin_cases m
    · exact broute33
    · exact broute34
    · exact broute35
  · intro m; fin_cases m
    · exact from24
    · exact from25
    · exact from26
private theorem to9 : ToHRows (st 3396) (st 3392) := by
  exact ⟨(st 3395),(st 3394),(st 3393),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute36 : RouteL 2 0 (st 3392) (st 3388) :=
  (RouteL.next (s:=(st 3389)) (q:=(st 3391)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3390)) (q:=(st 3388)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3388))))
private theorem src9 : SourceRows true (st 3388) (fun m : Fin 3 => st (#[3376,3384,3369][m.val]!)) := by
  exact ⟨(st 3387),(st 3386),(fun b : Bool => if b then (st 3385) else (st 3377)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute37 : RouteR 0 2 (st 3376) (st 3372) :=
  (RouteR.next (s:=(st 3374)) (q:=(st 3375)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3373)) (q:=(st 3372)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3372))))
private theorem broute38 : RouteR 0 2 (st 3384) (st 3380) :=
  (RouteR.next (s:=(st 3382)) (q:=(st 3383)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3381)) (q:=(st 3380)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3380))))
private theorem broute39 : RouteR 0 2 (st 3369) (st 3365) :=
  (RouteR.next (s:=(st 3367)) (q:=(st 3368)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3366)) (q:=(st 3365)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3365))))
private theorem from27 : FromHRows (st 3372) (st 655) := by
  exact ⟨(st 3370),(st 3371),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from28 : FromHRows (st 3380) (st 3672) := by
  exact ⟨(st 3378),(st 3379),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from29 : FromHRows (st 3365) (st 5948) := by
  exact ⟨(st 3363),(st 3364),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph9 : PhysicalRows true (st 3396) (fun m => getExit ⟨0,by decide⟩ true m) := by
  refine ⟨(st 3392),(st 3388),(fun m : Fin 3 => st (#[3376,3384,3369][m.val]!)),(fun m : Fin 3 => st (#[3372,3380,3365][m.val]!)),to9,broute36,src9,?_,?_⟩
  · intro m; fin_cases m
    · exact broute37
    · exact broute38
    · exact broute39
  · intro m; fin_cases m
    · exact from27
    · exact from28
    · exact from29
private theorem to10 : ToHRows (st 3502) (st 3498) := by
  exact ⟨(st 3501),(st 3500),(st 3499),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute40 : RouteL 2 0 (st 3498) (st 3494) :=
  (RouteL.next (s:=(st 3495)) (q:=(st 3497)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3496)) (q:=(st 3494)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3494))))
private theorem src10 : SourceRows true (st 3494) (fun m : Fin 3 => st (#[3482,3490,3475][m.val]!)) := by
  exact ⟨(st 3493),(st 3492),(fun b : Bool => if b then (st 3491) else (st 3483)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute41 : RouteR 0 2 (st 3482) (st 3478) :=
  (RouteR.next (s:=(st 3480)) (q:=(st 3481)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3479)) (q:=(st 3478)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3478))))
private theorem broute42 : RouteR 0 2 (st 3490) (st 3486) :=
  (RouteR.next (s:=(st 3488)) (q:=(st 3489)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3487)) (q:=(st 3486)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3486))))
private theorem broute43 : RouteR 0 2 (st 3475) (st 3471) :=
  (RouteR.next (s:=(st 3473)) (q:=(st 3474)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3472)) (q:=(st 3471)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3471))))
private theorem from30 : FromHRows (st 3478) (st 1108) := by
  exact ⟨(st 3476),(st 3477),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from31 : FromHRows (st 3486) (st 3876) := by
  exact ⟨(st 3484),(st 3485),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from32 : FromHRows (st 3471) (st 6084) := by
  exact ⟨(st 3469),(st 3470),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph10 : PhysicalRows true (st 3502) (fun m => getExit ⟨1,by decide⟩ true m) := by
  refine ⟨(st 3498),(st 3494),(fun m : Fin 3 => st (#[3482,3490,3475][m.val]!)),(fun m : Fin 3 => st (#[3478,3486,3471][m.val]!)),to10,broute40,src10,?_,?_⟩
  · intro m; fin_cases m
    · exact broute41
    · exact broute42
    · exact broute43
  · intro m; fin_cases m
    · exact from30
    · exact from31
    · exact from32
private theorem to11 : ToHRows (st 3604) (st 3600) := by
  exact ⟨(st 3603),(st 3602),(st 3601),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute44 : RouteL 2 0 (st 3600) (st 3596) :=
  (RouteL.next (s:=(st 3597)) (q:=(st 3599)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3598)) (q:=(st 3596)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3596))))
private theorem src11 : SourceRows true (st 3596) (fun m : Fin 3 => st (#[3584,3592,3577][m.val]!)) := by
  exact ⟨(st 3595),(st 3594),(fun b : Bool => if b then (st 3593) else (st 3585)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute45 : RouteR 0 2 (st 3584) (st 3580) :=
  (RouteR.next (s:=(st 3582)) (q:=(st 3583)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3581)) (q:=(st 3580)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3580))))
private theorem broute46 : RouteR 0 2 (st 3592) (st 3588) :=
  (RouteR.next (s:=(st 3590)) (q:=(st 3591)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3589)) (q:=(st 3588)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3588))))
private theorem broute47 : RouteR 0 2 (st 3577) (st 3573) :=
  (RouteR.next (s:=(st 3575)) (q:=(st 3576)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3574)) (q:=(st 3573)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3573))))
private theorem from33 : FromHRows (st 3580) (st 1405) := by
  exact ⟨(st 3578),(st 3579),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from34 : FromHRows (st 3588) (st 4034) := by
  exact ⟨(st 3586),(st 3587),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from35 : FromHRows (st 3573) (st 6198) := by
  exact ⟨(st 3571),(st 3572),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph11 : PhysicalRows true (st 3604) (fun m => getExit ⟨2,by decide⟩ true m) := by
  refine ⟨(st 3600),(st 3596),(fun m : Fin 3 => st (#[3584,3592,3577][m.val]!)),(fun m : Fin 3 => st (#[3580,3588,3573][m.val]!)),to11,broute44,src11,?_,?_⟩
  · intro m; fin_cases m
    · exact broute45
    · exact broute46
    · exact broute47
  · intro m; fin_cases m
    · exact from33
    · exact from34
    · exact from35
private theorem to12 : ToHRows (st 3706) (st 3702) := by
  exact ⟨(st 3705),(st 3704),(st 3703),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute48 : RouteL 2 0 (st 3702) (st 3698) :=
  (RouteL.next (s:=(st 3699)) (q:=(st 3701)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3700)) (q:=(st 3698)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3698))))
private theorem src12 : SourceRows true (st 3698) (fun m : Fin 3 => st (#[3686,3694,3679][m.val]!)) := by
  exact ⟨(st 3697),(st 3696),(fun b : Bool => if b then (st 3695) else (st 3687)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute49 : RouteR 0 2 (st 3686) (st 3682) :=
  (RouteR.next (s:=(st 3684)) (q:=(st 3685)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3683)) (q:=(st 3682)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3682))))
private theorem broute50 : RouteR 0 2 (st 3694) (st 3690) :=
  (RouteR.next (s:=(st 3692)) (q:=(st 3693)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3691)) (q:=(st 3690)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3690))))
private theorem broute51 : RouteR 0 2 (st 3679) (st 3675) :=
  (RouteR.next (s:=(st 3677)) (q:=(st 3678)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3676)) (q:=(st 3675)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3675))))
private theorem from36 : FromHRows (st 3682) (st 1507) := by
  exact ⟨(st 3680),(st 3681),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from37 : FromHRows (st 3690) (st 4133) := by
  exact ⟨(st 3688),(st 3689),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from38 : FromHRows (st 3675) (st 6266) := by
  exact ⟨(st 3673),(st 3674),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph12 : PhysicalRows true (st 3706) (fun m => getExit ⟨3,by decide⟩ true m) := by
  refine ⟨(st 3702),(st 3698),(fun m : Fin 3 => st (#[3686,3694,3679][m.val]!)),(fun m : Fin 3 => st (#[3682,3690,3675][m.val]!)),to12,broute48,src12,?_,?_⟩
  · intro m; fin_cases m
    · exact broute49
    · exact broute50
    · exact broute51
  · intro m; fin_cases m
    · exact from36
    · exact from37
    · exact from38
private theorem to13 : ToHRows (st 3808) (st 3804) := by
  exact ⟨(st 3807),(st 3806),(st 3805),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute52 : RouteL 2 0 (st 3804) (st 3800) :=
  (RouteL.next (s:=(st 3801)) (q:=(st 3803)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3802)) (q:=(st 3800)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3800))))
private theorem src13 : SourceRows true (st 3800) (fun m : Fin 3 => st (#[3788,3796,3781][m.val]!)) := by
  exact ⟨(st 3799),(st 3798),(fun b : Bool => if b then (st 3797) else (st 3789)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute53 : RouteR 0 2 (st 3788) (st 3784) :=
  (RouteR.next (s:=(st 3786)) (q:=(st 3787)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3785)) (q:=(st 3784)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3784))))
private theorem broute54 : RouteR 0 2 (st 3796) (st 3792) :=
  (RouteR.next (s:=(st 3794)) (q:=(st 3795)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3793)) (q:=(st 3792)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3792))))
private theorem broute55 : RouteR 0 2 (st 3781) (st 3777) :=
  (RouteR.next (s:=(st 3779)) (q:=(st 3780)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 3778)) (q:=(st 3777)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3777))))
private theorem from39 : FromHRows (st 3784) (st 944) := by
  exact ⟨(st 3782),(st 3783),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from40 : FromHRows (st 3792) (st 975) := by
  exact ⟨(st 3790),(st 3791),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from41 : FromHRows (st 3777) (st 1006) := by
  exact ⟨(st 3775),(st 3776),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph13 : PhysicalRows true (st 3808) (fun m => getExit ⟨4,by decide⟩ true m) := by
  refine ⟨(st 3804),(st 3800),(fun m : Fin 3 => st (#[3788,3796,3781][m.val]!)),(fun m : Fin 3 => st (#[3784,3792,3777][m.val]!)),to13,broute52,src13,?_,?_⟩
  · intro m; fin_cases m
    · exact broute53
    · exact broute54
    · exact broute55
  · intro m; fin_cases m
    · exact from39
    · exact from40
    · exact from41
private theorem to14 : ToHRows (st 3887) (st 3883) := by
  exact ⟨(st 3886),(st 3885),(st 3884),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute56 : RouteL 2 0 (st 3883) (st 3879) :=
  (RouteL.next (s:=(st 3880)) (q:=(st 3882)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3881)) (q:=(st 3879)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3879))))
private theorem src14 : SourceRows true (st 3879) (fun m : Fin 3 => st (#[1317,1325,1310][m.val]!)) := by
  exact ⟨(st 3878),(st 3877),(fun b : Bool => if b then (st 1326) else (st 1318)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem ph14 : PhysicalRows true (st 3887) (fun m => getExit ⟨5,by decide⟩ true m) := by
  refine ⟨(st 3883),(st 3879),(fun m : Fin 3 => st (#[1317,1325,1310][m.val]!)),(fun m : Fin 3 => st (#[1313,1321,1306][m.val]!)),to14,broute56,src14,?_,?_⟩
  · intro m; fin_cases m
    · exact broute25
    · exact broute26
    · exact broute27
  · intro m; fin_cases m
    · exact from18
    · exact from19
    · exact from20
private theorem to15 : ToHRows (st 3966) (st 3962) := by
  exact ⟨(st 3965),(st 3964),(st 3963),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute57 : RouteL 2 0 (st 3962) (st 3958) :=
  (RouteL.next (s:=(st 3959)) (q:=(st 3961)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 3960)) (q:=(st 3958)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 3958))))
private theorem src15 : SourceRows true (st 3958) (fun m : Fin 3 => st (#[1317,1325,1310][m.val]!)) := by
  exact ⟨(st 3957),(st 3956),(fun b : Bool => if b then (st 1326) else (st 1318)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem ph15 : PhysicalRows true (st 3966) (fun m => getExit ⟨6,by decide⟩ true m) := by
  refine ⟨(st 3962),(st 3958),(fun m : Fin 3 => st (#[1317,1325,1310][m.val]!)),(fun m : Fin 3 => st (#[1313,1321,1306][m.val]!)),to15,broute57,src15,?_,?_⟩
  · intro m; fin_cases m
    · exact broute25
    · exact broute26
    · exact broute27
  · intro m; fin_cases m
    · exact from18
    · exact from19
    · exact from20
private theorem to16 : ToHRows (st 4065) (st 4061) := by
  exact ⟨(st 4064),(st 4063),(st 4062),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute58 : RouteL 2 0 (st 4061) (st 4057) :=
  (RouteL.next (s:=(st 4058)) (q:=(st 4060)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4059)) (q:=(st 4057)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 4057))))
private theorem src16 : SourceRows true (st 4057) (fun m : Fin 3 => st (#[4045,4053,4041][m.val]!)) := by
  exact ⟨(st 4056),(st 4055),(fun b : Bool => if b then (st 4054) else (st 4046)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute59 : RouteR 0 2 (st 4045) (st 3020) :=
  (RouteR.next (s:=(st 4043)) (q:=(st 4044)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4042)) (q:=(st 3020)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 3020))))
private theorem broute60 : RouteR 0 2 (st 4053) (st 4049) :=
  (RouteR.next (s:=(st 4051)) (q:=(st 4052)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4050)) (q:=(st 4049)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 4049))))
private theorem broute61 : RouteR 0 2 (st 4041) (st 4037) :=
  (RouteR.next (s:=(st 4039)) (q:=(st 4040)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4038)) (q:=(st 4037)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 4037))))
private theorem from42 : FromHRows (st 3020) (st 2218) := by
  exact ⟨(st 3018),(st 3019),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from43 : FromHRows (st 4049) (st 4834) := by
  exact ⟨(st 4047),(st 4048),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from44 : FromHRows (st 4037) (st 6935) := by
  exact ⟨(st 4035),(st 4036),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph16 : PhysicalRows true (st 4065) (fun m => getExit ⟨7,by decide⟩ true m) := by
  refine ⟨(st 4061),(st 4057),(fun m : Fin 3 => st (#[4045,4053,4041][m.val]!)),(fun m : Fin 3 => st (#[3020,4049,4037][m.val]!)),to16,broute58,src16,?_,?_⟩
  · intro m; fin_cases m
    · exact broute59
    · exact broute60
    · exact broute61
  · intro m; fin_cases m
    · exact from42
    · exact from43
    · exact from44
private theorem to17 : ToHRows (st 4949) (st 4945) := by
  exact ⟨(st 4948),(st 4947),(st 4946),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem broute62 : RouteL 2 0 (st 4945) (st 4941) :=
  (RouteL.next (s:=(st 4942)) (q:=(st 4944)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.next (s:=(st 4943)) (q:=(st 4941)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteL.nil 0 (st 4941))))
private theorem src17 : SourceRows true (st 4941) (fun m : Fin 3 => st (#[4929,4937,4922][m.val]!)) := by
  exact ⟨(st 4940),(st 4939),(fun b : Bool => if b then (st 4938) else (st 4930)),by decide,by decide,by decide,
    (by intro b; cases b <;> decide),rfl,(by intro b; cases b <;> rfl),rfl,rfl,
    (by intro b; cases b <;> rfl),(by intro b c; cases b <;> cases c <;> rfl),(by intro b; cases b <;> rfl)⟩
private theorem broute63 : RouteR 0 2 (st 4929) (st 4925) :=
  (RouteR.next (s:=(st 4927)) (q:=(st 4928)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4926)) (q:=(st 4925)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 4925))))
private theorem broute64 : RouteR 0 2 (st 4937) (st 4933) :=
  (RouteR.next (s:=(st 4935)) (q:=(st 4936)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4934)) (q:=(st 4933)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 4933))))
private theorem broute65 : RouteR 0 2 (st 4922) (st 4918) :=
  (RouteR.next (s:=(st 4920)) (q:=(st 4921)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.next (s:=(st 4919)) (q:=(st 4918)) (by decide) (by decide) rfl (by intro b; cases b <;> rfl) rfl (RouteR.nil 2 (st 4918))))
private theorem from45 : FromHRows (st 4925) (st 2484) := by
  exact ⟨(st 4923),(st 4924),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from46 : FromHRows (st 4933) (st 2506) := by
  exact ⟨(st 4931),(st 4932),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem from47 : FromHRows (st 4918) (st 2528) := by
  exact ⟨(st 4916),(st 4917),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem ph17 : PhysicalRows true (st 4949) (fun m => getExit ⟨8,by decide⟩ true m) := by
  refine ⟨(st 4945),(st 4941),(fun m : Fin 3 => st (#[4929,4937,4922][m.val]!)),(fun m : Fin 3 => st (#[4925,4933,4918][m.val]!)),to17,broute62,src17,?_,?_⟩
  · intro m; fin_cases m
    · exact broute63
    · exact broute64
    · exact broute65
  · intro m; fin_cases m
    · exact from45
    · exact from46
    · exact from47
end BackendRows
private theorem physical_code (site : Fin 9) (bit : Bool) :
    PhysicalRows bit (getBody site (bm bit)) (fun m => getExit site bit m) := by
  cases bit <;> fin_cases site
  · exact ph0
  · exact ph1
  · exact ph2
  · exact ph3
  · exact ph4
  · exact ph5
  · exact ph6
  · exact ph7
  · exact ph8
  · exact ph9
  · exact ph10
  · exact ph11
  · exact ph12
  · exact ph13
  · exact ph14
  · exact ph15
  · exact ph16
  · exact ph17
private theorem body_virtual (site : Fin 9) : getBody site ⟨2,by decide⟩=getExit site false ⟨2,by decide⟩ := by
  fin_cases site <;> rfl
private theorem exits_safe (site : Fin 9) (bit : Bool) (mode : Fin 3) : 4 ≤ (getExit site bit mode).val := by
  fin_cases site <;> cases bit <;> fin_cases mode <;> decide

theorem reader (site : Fin 9) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r v u c N B P : Nat) (source : Fin S → Bool)
    (hv : v+u ≤ r) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (remaining : ∀ i,D 4 < i → i < D 5 → T i=some (decide (i-D 4 ≤ v)))
    (consumed : ∀ i,D 11 < i → i < D 12 → T i=some (decide (i-D 11 ≤ u)))
    (eof : T S=none) (left : T L=none) (right : T H=none) (fence : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b)
    (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none)
    (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let C : Nat → Option Bool:=fun i => if i=D 11+u+1 then some true else if i=D 4+v then some false else T i
    let initial : Config 7500 N B:=⟨getEntry site (SerializedBody.sourceMode source c),⟨D 0,h0⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 64*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨(if v=0 then getAbort (SerializedBody.sourceMode source c) else
          getExit site (Pnp4.Frontier.ContractExpansion.padRead source c) (SerializedBody.sourceMode source (c+1))),
        ⟨D 0,h0⟩,fun i=>if v=0 then T i.val else if c < S then
          if i.val=c+1 then none else if i.val=c then some (Pnp4.Frontier.ContractExpansion.padRead source c) else C i.val
          else C i.val⟩ ∧ ∀ j,j ≤ t → 4 ≤ (SerializedBody.machine.run j initial).state.val := by
  exact reader_core physical_code body_virtual exits_safe site D T S L H Q F r v u c N B P source hv sl lh positive arena anchor rise mono blank cells len4 len11 remaining consumed eof left right fence reg ass marks gap hole src room fit h0
#print axioms SerializedBodyRefinement.reader
theorem reader_mirror (call : Fin 9) (d : Nat → Nat) (mem : Nat → Option Bool)
    (sourceN leftEnd rightEnd paid fencePos cap remainingCount consumedCount cursor inputN budget extent : Nat)
    (word : Fin sourceN → Bool) (bounded : remainingCount+consumedCount ≤ cap)
    (sourceBeforeLeft : sourceN < leftEnd) (leftBeforeRight : leftEnd < rightEnd)
    (paidPositive : 0 < paid) (paidBeforeFence : rightEnd+paid < fencePos)
    (delimiterZero : d 0=fencePos+1) (ascending : ∀ j,j < 12 → d j < d (j+1))
    (ordered : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b)
    (separators : ∀ j,j ≤ 12 → mem (d j)=none)
    (occupied : ∀ j i,j < 12 → d j < i → i < d (j+1) → ∃ b,mem i=some b)
    (widthRemaining : d 5=d 4+cap+1) (widthConsumed : d 12=d 11+cap+1)
    (remainingBits : ∀ i,d 4 < i → i < d 5 → mem i=some (decide (i-d 4 ≤ remainingCount)))
    (consumedBits : ∀ i,d 11 < i → i < d 12 → mem i=some (decide (i-d 11 ≤ consumedCount)))
    (physicalEOF : mem sourceN=none) (leftBlank : mem leftEnd=none) (rightBlank : mem rightEnd=none)
    (fenceCell : mem fencePos=some false)
    (register : ∀ i,sourceN < i → i < leftEnd → ∃ b,mem i=some b)
    (assignment : ∀ i,leftEnd < i → i < rightEnd → ∃ b,mem i=some b)
    (paidCells : ∀ i,rightEnd < i → i ≤ rightEnd+paid → mem i=some true)
    (clearGap : ∀ i,rightEnd+paid < i → i < fencePos → mem i=none)
    (cursorHole : cursor < sourceN → mem cursor=none)
    (unread : ∀ i,cursor < i → ∀ hi : i < sourceN,mem i=some (word ⟨i,hi⟩))
    (room : d 12 ≤ extent) (fits : extent < tapeLength inputN budget)
    (headFits : d 0 < tapeLength inputN budget) :
    let changed : Nat → Option Bool:=fun i => if i=d 11+consumedCount+1 then some true
      else if i=d 4+remainingCount then some false else mem i
    let begin : Config 7500 inputN budget:=
      ⟨getEntry call (SerializedBody.sourceMode word cursor),⟨d 0,headFits⟩,fun i=>mem i.val⟩
    ∃ ticks,ticks ≤ 64*(extent+1) ∧ SerializedBody.machine.run ticks begin=
      ⟨(if remainingCount=0 then getAbort (SerializedBody.sourceMode word cursor) else
          getExit call (Pnp4.Frontier.ContractExpansion.padRead word cursor)
            (SerializedBody.sourceMode word (cursor+1))),
        ⟨d 0,headFits⟩,fun i=>if remainingCount=0 then mem i.val else if cursor < sourceN then
          if i.val=cursor+1 then none else if i.val=cursor then
            some (Pnp4.Frontier.ContractExpansion.padRead word cursor) else changed i.val
          else changed i.val⟩ ∧ ∀ j,j ≤ ticks → 4 ≤ (SerializedBody.machine.run j begin).state.val := by
  exact reader call d mem sourceN leftEnd rightEnd paid fencePos cap remainingCount consumedCount cursor inputN budget extent word bounded sourceBeforeLeft leftBeforeRight paidPositive paidBeforeFence delimiterZero ascending ordered separators occupied widthRemaining widthConsumed remainingBits consumedBits physicalEOF leftBlank rightBlank fenceCell register assignment paidCells clearGap cursorHole unread room fits headFits
#print axioms SerializedBodyRefinement.reader_mirror
theorem sourceMode_eq_1_mirror {length : Nat} (bits : Fin length → Bool) (offset : Nat) :
    SerializedBody.sourceMode bits offset =
      if physical : offset < length then
        if bits ⟨offset,physical⟩=true then (⟨1,by decide⟩ : Fin 3) else ⟨0,by decide⟩
      else ⟨2,by decide⟩ := by
  rfl
#print axioms SerializedBody.sourceMode.eq_1
#print axioms SerializedBodyRefinement.sourceMode_eq_1_mirror
end SerializedBodyRefinement

open Lean in
run_cmd do
  let e ← getEnv
  for n in e.header.moduleNames do logInfo m!"current-imported|{n}"
  for (n,ci) in e.constants.toList do
    let owner := match e.getModuleIdxFor? n with
      | some i => e.header.moduleNames[i]!
      | none => e.mainModule
    if owner.toString.startsWith "SerializedBodyRefinement." then
      let s:=n.toString
      let kind:=if s.startsWith "_private." then "private" else if n.isInternal ||
        (s.splitOn ".").any (fun c => "_".isPrefixOf c || "match_".isPrefixOf c)
        then "internal" else "public"
      let ck:=match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiomatic" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
      logInfo m!"current-owner|{kind}|{owner}|{n}|{ck}"
      logInfo m!"current-owner-type|{n}|{ci.type}"
      logInfo m!"current-owner-axioms|{n}|{← Lean.collectAxioms n}"
  logInfo m!"registered-option|maxHeartbeats|{Lean.maxHeartbeats.get (← getOptions)}"
  logInfo m!"registered-option|maxRecDepth|{Lean.maxRecDepth.get (← getOptions)}"
