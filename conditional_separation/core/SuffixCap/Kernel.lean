import SuffixCap.Rows
namespace SuffixCap
open Pnp3.Complexity.Uniform.V1
open Lean Elab Tactic
set_option maxRecDepth 10000
private structure Node (k : Nat) where
  state : Fin (Cursor.stateCount k)
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {k N B : Nat} (c : Node k) (h : c.head < tapeLength N B) : Config (Cursor.stateCount k) N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (k P : Nat) (c d : Node k) : Prop where
  safe : c.state.val < 98
  before : c.head   ≤   P
  after : d.head   ≤   P
  row : ((Cursor.machine k).step c.state (c.tape c.head)).1 = d.state
  move : dest c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.1
private inductive Path (k P : Nat) : Nat → Node k → Node k → Prop
  | nil (c) (h : c.head   ≤   P) : Path k P 0 c c
  | cons {t c d e} : Edge k P c d → Path k P t d e → Path k P (t+1) c e
namespace Path
private theorem bounds {k P t c d} (h : Path k P t c d) : c.head   ≤   P ∧ d.head   ≤   P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {k P t u c d e} (h : Path k P t c d) (g : Path k P u d e) :
    Path k P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {k N B P t c d} (h : Path k P t c d) (hp : P < tapeLength N B) :
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
        have hr : c.head+1 < tapeLength N B := by omega
        simp only [moveHead,embed,hr,↓reduceDIte]
        exact hm
    · funext i
      dsimp only [UniformTM.stepConfig,embed]
      rw [e.tape]
      simp only [put,Fin.ext_iff]
  suffices aux : ∀ (hc : c.head < tapeLength N B) (hd : d.head < tapeLength N B),
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
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hs : s.val < 98) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hs,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
/-- One exact public row that preserves the scanned symbol. -/
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hs : s.val < 98) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hs hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (hs : s.val < 98) (fit : h+r   ≤   P) (rows : ∀ i, h   ≤   i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right hs (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (hs : s.val < 98) (fit : low+r   ≤   P) (rows : ∀ i, low < i → i   ≤   low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left hs (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private theorem small_mod (k i : Nat) (h : i  ≤  98) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private def base (b : Bool) : Nat := if b then 83 else 68
private structure Frame (T : Nat → Option Bool) (p S z n Q F r : Nat) : Prop where
  pos : 0 < p
  end_lt : p < S
  rem : r=S-p
  paid : 0 < Q
  room : S+z+n+3+Q < F
  source : ∀ i, p  ≤  i → i < S → ∃ b, T i=some b
  eof : T S=none
  reg : ∀ i, S < i → i < S+z+2 → T i=some false
  sep : T (S+z+2)=none
  assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b
  right : T (S+z+n+3)=none
  marks : ∀ i, S+z+n+3 < i → i  ≤  S+z+n+3+Q → T i=some true
  gap : ∀ i, S+z+n+3+Q < i → i < F → T i=none
  fence : T F=some false
  fresh : ∀ i, F < i → i  ≤  F+r+2 → T i=none
private theorem image_old (T : Nat → Option Bool) (F c i : Nat) (hi : i  ≤  F+1) :
    Target.image T F c i=T i := by simp [Target.image,show ¬(F+2 ≤ i ∧ i < F+c+2) by omega]
private theorem image_add (T : Nat → Option Bool) (F c h : Nat) (hh : h < F)
    :
    put (put (Target.image T F c) h none) (F+c+2) (some true)=
      put (Target.image T F (c+1)) h none := by
  funext i
  by_cases hi : i=h
  · subst i; simp [put,show h ≠ F+c+2 by omega]
  · by_cases he : i=F+c+2
    · subst i; simp [put,hi,Target.image]
    · have eq : (F+2 ≤ i ∧ i < F+(c+1)+2) ↔ (F+2 ≤ i ∧ i < F+c+2) := by omega
      simp only [put,hi,he,↓reduceIte,Target.image,eq]
private theorem round_path (k : Nat) (T : Nat → Option Bool) (p S z n Q F r c h : Nat)
    (fr : Frame T p S z n Q F r) (hc : c < r) (hh : h=p+c)
    (b : Bool) (bit : T h=some b) :
    Path k (F+r+2) (2*(F-h)+2*c+5)
      ⟨Cursor.q k (base b),h+1,put (Target.image T F c) h none⟩
      ⟨Cursor.q k (base b+14),h+1,Target.image T F (c+1)⟩ := by
  rcases count_rows k b with ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,_,_⟩
  let P := F+r+2
  let H := S+z+n+3
  let D := put (Target.image T F c) h none
  let E := Target.image T F (c+1)
  let V := put E h none
  have hS : h < S := by have := fr.rem; omega
  have hF : h < F := by have := fr.room; omega
  have bounds := fr.room
  have paid := fr.paid
  have pos := fr.pos
  have safe (j : Nat) (hj : j ≤ 14) : (Cursor.q k (base b+j)).val < 98 := by
    simp only [Cursor.q]
    rw [small_mod k _ (by cases b <;> simp [base] <;> omega)]
    cases b <;> simp [base] <;> omega
  have oldD (i : Nat) (hi : i ≤ F+1) (ne : i ≠ h) : D i=T i := by
    simp only [D,put,ne,↓reduceIte,image_old T F c i hi]
  have oldV (i : Nat) (hi : i ≤ F+1) (ne : i ≠ h) : V i=T i := by
    simp only [V,E,put,ne,↓reduceIte,image_old T F (c+1) i hi]
  have sr := sweepR (Cursor.q k (base b)) D (h+1) (S-h-1) (safe 0 (by omega))
    (P := P) (by dsimp [P]; omega) (by
      intro i lo hi; obtain ⟨v,hv⟩ := fr.source i (by omega) (by omega)
      rw [oldD i (by omega) (by omega),hv]; exact r0 v)
  have eS : h+1+(S-h-1)=S := by omega
  rw [eS] at sr
  have a := keep (Cursor.q k (base b)) (Cursor.q k (base b+1)) S (S+1) D .right
    (safe 0 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by rw [oldD S (by omega) (by omega),fr.eof]; exact r1) rfl
  have regs := sweepR (Cursor.q k (base b+1)) D (S+1) (z+1) (safe 1 (by omega))
    (P := P) (by dsimp [P]; omega) (by
      intro i lo hi; rw [oldD i (by omega) (by omega),fr.reg i (by omega) (by omega)]; exact r2)
  rw [show S+1+(z+1)=S+z+2 by omega] at regs
  have sep := keep (Cursor.q k (base b+1)) (Cursor.q k (base b+2)) (S+z+2) (S+z+3) D .right
    (safe 1 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P,H] at *; omega)
    (by rw [oldD _ (by omega) (by omega),fr.sep]; exact r3) rfl
  have digits := sweepR (Cursor.q k (base b+2)) D (S+z+3) n (safe 2 (by omega))
    (P := P) (by dsimp [P,H] at *; omega) (by
      intro i lo hi; obtain ⟨v,hv⟩ := fr.assn i (by omega) (by omega)
      rw [oldD i (by omega) (by omega),hv]; exact r4 v)
  rw [show S+z+3+n=H by dsimp [H]; omega] at digits
  have rh := keep (Cursor.q k (base b+2)) (Cursor.q k (base b+3)) H H D .stay
    (safe 2 (by omega)) (P := P) (by dsimp [P,H]; omega) (by dsimp [P,H]; omega)
    (by rw [oldD _ (by dsimp [H]; omega) (by dsimp [H]; omega),fr.right]; exact r5) rfl
  have hr := keep (Cursor.q k (base b+3)) (Cursor.q k (base b+4)) H (H+1) D .right
    (safe 3 (by omega)) (P := P) (by dsimp [P,H]; omega) (by dsimp [P,H]; omega)
    (by rw [oldD _ (by dsimp [H]; omega) (by dsimp [H]; omega),fr.right]; exact r6) rfl
  have outward := sweepR (Cursor.q k (base b+4)) D (H+1) (F-H-1) (safe 4 (by omega))
    (P := P) (by dsimp [P,H]; omega) (by
      intro i lo hi
      rw [oldD i (by omega) (by dsimp [H] at lo; omega)]
      by_cases im : i ≤ H+Q
      · rw [fr.marks i (by dsimp [H] at lo; omega) im]; exact r8
      · rw [fr.gap i (by dsimp [H] at *; omega) (by omega)]; exact r7)
  rw [show H+1+(F-H-1)=F by dsimp [H] at *; omega] at outward
  have ff := keep (Cursor.q k (base b+4)) (Cursor.q k (base b+5)) F (F+1) D .right
    (safe 4 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by rw [oldD F (by omega) (by omega),fr.fence]; exact r9) rfl
  have gg := keep (Cursor.q k (base b+5)) (Cursor.q k (base b+6)) (F+1) (F+2) D .right
    (safe 5 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by rw [oldD _ le_rfl (by omega),fr.fresh _ (by omega) (by omega)]; exact r10) rfl
  have ms := sweepR (Cursor.q k (base b+6)) D (F+2) c (safe 6 (by omega))
    (P := P) (by dsimp [P]; omega) (by
      intro i lo hi
      have vi : D i=some true := by simp [D,put,Target.image,show i ≠ h by omega,lo,show i < F+c+2 by omega]
      rw [vi]; exact r11)
  rw [show F+2+c=F+c+2 by omega] at ms
  have fresh : D (F+c+2)=none := by
    simp [D,put,Target.image,show F+c+2 ≠ h by omega,fr.fresh (F+c+2) (by omega) (by omega)]
  have app := hop (Cursor.q k (base b+6)) (Cursor.q k (base b+7)) (F+c+2) (F+c+1) D (some true) .left
    (safe 6 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by rw [fresh]; exact r12) (by simp [dest])
  have added : put D (F+c+2) (some true)=V := image_add T F c h hF
  rw [added] at app
  have backMarks := sweepL (Cursor.q k (base b+7)) V (F+1) c (safe 7 (by omega))
    (P := P) (by dsimp [P]; omega) (by
      intro i lo hi
      have vi : V i=some true := by simp [V,E,put,Target.image,show i ≠ h by omega,show F+2 ≤ i by omega,show i < F+(c+1)+2 by omega]
      rw [vi]; exact r13)
  rw [show F+1+c=F+c+1 by omega] at backMarks
  have bg := keep (Cursor.q k (base b+7)) (Cursor.q k (base b+8)) (F+1) F V .left
    (safe 7 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by rw [oldV _ le_rfl (by omega),fr.fresh _ (by omega) (by omega)]; exact r14) (by simp [dest])
  have bf := keep (Cursor.q k (base b+8)) (Cursor.q k (base b+9)) F (F-1) V .left
    (safe 8 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by rw [oldV F (by omega) (by omega),fr.fence]; exact r15) rfl
  have blankGap := sweepL (Cursor.q k (base b+9)) V (H+Q) (F-1-(H+Q)) (safe 9 (by omega))
    (P := P) (by dsimp [P,H]; omega) (by
      intro i lo hi; rw [oldV i (by omega) (by dsimp [H] at lo; omega),fr.gap i lo (by omega)]; exact r16)
  rw [show H+Q+(F-1-(H+Q))=F-1 by dsimp [H] at *; omega] at blankGap
  have lastMark := keep (Cursor.q k (base b+9)) (Cursor.q k (base b+10)) (H+Q) (H+Q-1) V .left
    (safe 9 (by omega)) (P := P) (by dsimp [P,H]; omega) (by dsimp [P,H]; omega)
    (by rw [oldV _ (by dsimp [H] at *; omega) (by dsimp [H]; omega),fr.marks _ (by dsimp [H]; omega) (by dsimp [H]; omega)]; exact r17) rfl
  have oldMarks := sweepL (Cursor.q k (base b+10)) V H (Q-1) (safe 10 (by omega))
    (P := P) (by dsimp [P,H]; omega) (by
      intro i lo hi; rw [oldV i (by dsimp [H] at *; omega) (by dsimp [H] at lo; omega),fr.marks i lo (by omega)]; exact r18)
  rw [show H+(Q-1)=H+Q-1 by omega] at oldMarks
  have bh := keep (Cursor.q k (base b+10)) (Cursor.q k (base b+11)) H (H-1) V .left
    (safe 10 (by omega)) (P := P) (by dsimp [P,H]; omega) (by dsimp [P,H]; omega)
    (by rw [oldV _ (by dsimp [H]; omega) (by dsimp [H]; omega),fr.right]; exact r19) rfl
  have backDigits := sweepL (Cursor.q k (base b+11)) V (S+z+2) n (safe 11 (by omega))
    (P := P) (by dsimp [P,H]; omega) (by
      intro i lo hi; obtain ⟨v,hv⟩ := fr.assn i lo (by omega)
      rw [oldV i (by omega) (by omega),hv]; exact r20 v)
  rw [show S+z+2+n=H-1 by dsimp [H]; omega] at backDigits
  have bl := keep (Cursor.q k (base b+11)) (Cursor.q k (base b+12)) (S+z+2) (S+z+1) V .left
    (safe 11 (by omega)) (P := P) (by dsimp [P,H]; omega) (by dsimp [P,H]; omega)
    (by rw [oldV _ (by omega) (by omega),fr.sep]; exact r21) (by simp [dest])
  have backReg := sweepL (Cursor.q k (base b+12)) V S (z+1) (safe 12 (by omega))
    (P := P) (by dsimp [P,H]; omega) (by
      intro i lo hi; rw [oldV i (by omega) (by omega),fr.reg i lo (by omega)]; exact r22)
  rw [show S+(z+1)=S+z+1 by omega] at backReg
  have bs := keep (Cursor.q k (base b+12)) (Cursor.q k (base b+13)) S (S-1) V .left
    (safe 12 (by omega)) (P := P) (by dsimp [P,H]; omega) (by dsimp [P,H]; omega)
    (by rw [oldV S (by omega) (by omega),fr.eof]; exact r23) rfl
  have backSource := sweepL (Cursor.q k (base b+13)) V h (S-1-h) (safe 13 (by omega))
    (P := P) (by dsimp [P,H]; omega) (by
      intro i lo hi; obtain ⟨v,hv⟩ := fr.source i (by omega) (by omega)
      rw [oldV i (by omega) (by omega),hv]; exact r24 v)
  rw [show h+(S-1-h)=S-1 by omega] at backSource
  have restore := hop (Cursor.q k (base b+13)) (Cursor.q k (base b+14)) h (h+1) V (some b) .right
    (safe 13 (by omega)) (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by rw [show V h=none by simp [V,put]]; exact r25) rfl
  have restored : put V h (some b)=E := by
    funext i; by_cases hi : i=h
    · subst i; simp [V,E,put,image_old T F (c+1) h (by omega),bit]
    · simp [V,put,hi]
  rw [restored] at restore
  have wholePath := sr.append a |>.append regs |>.append sep |>.append digits |>.append rh |>.append hr
    |>.append outward |>.append ff |>.append gg |>.append ms |>.append app |>.append backMarks
    |>.append bg |>.append bf |>.append blankGap |>.append lastMark |>.append oldMarks |>.append bh
    |>.append backDigits |>.append bl |>.append backReg |>.append bs |>.append backSource |>.append restore
  convert wholePath using 1
  dsimp [P,E,H] at *
  omega
namespace Path
private theorem first {k N B P t c d} (path : Path k P t c d) (hp : P < tapeLength N B)
    (u : Nat) (hu : u < t) :
    ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val < 98 := by
  induction path generalizing u with
  | nil => omega
  | @cons t c d e edge rest ih =>
    cases u with
    | zero => exact edge.safe
    | succ u =>
      have one : Path k P 1 c d := Path.cons edge (Path.nil d edge.after)
      rw [show u+1=1+u by omega,UniformTM.run_add,one.execute hp]
      exact ih u (by omega)
end Path
private theorem count_iteration (k : Nat) (T : Nat → Option Bool) (p S z n Q F r : Nat)
    (fr : Frame T p S z n Q F r) (d c : Nat) (hd : 0 < d) (hr : c+d=r)
    (b : Bool) (bit : T (p+c)=some b) :
    Path k (F+r+2) (d*(2*(F-p)+6))
      ⟨Cursor.q k (base b),p+c+1,put (Target.image T F c) (p+c) none⟩
      ⟨Cursor.rReady k,S,Target.image T F r⟩ := by
  induction d generalizing c b with
  | zero => omega
  | succ d ih =>
    have hc : c < r := by omega
    have hs : p+c < S := by have := fr.rem; omega
    have hF : p+c < F := by have := fr.room; omega
    have safe : (Cursor.q k (base b+14)).val < 98 := by
      simp only [Cursor.q]
      rw [small_mod k _ (by cases b <;> simp [base])]
      cases b <;> simp [base]
    have round := round_path k T p S z n Q F r c (p+c) fr hc rfl b bit
    have unit : 2*(F-(p+c))+2*c+5+1=2*(F-p)+6 := by omega
    by_cases last : d=0
    · subst d
      have cr : c+1=r := by omega
      have next : p+c+1=S := by have := fr.rem; omega
      have eof : Target.image T F (c+1) (p+c+1)=none := by
        rw [image_old T F (c+1) _ (by have := fr.room; omega),next,fr.eof]
      have donePath := keep (Cursor.q k (base b+14)) (Cursor.rReady k) (p+c+1) (p+c+1)
        (Target.image T F (c+1)) .stay safe (P := F+r+2) (by omega) (by omega)
        (by rw [eof]; exact (count_rows k b).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
      have whole := round.append donePath
      simpa only [Nat.zero_add,Nat.one_mul,unit,next,cr] using whole
    · obtain ⟨v,hv⟩ := fr.source (p+c+1) (by omega) (by have := fr.rem; omega)
      have src : Target.image T F (c+1) (p+c+1)=some v := by
        rw [image_old T F (c+1) _ (by have := fr.room; omega),hv]
      have lift := hop (Cursor.q k (base b+14)) (Cursor.q k (base v)) (p+c+1) (p+c+2)
        (Target.image T F (c+1)) none .right safe (P := F+r+2) (by omega) (by omega)
        (by rw [src]; exact (count_rows k b).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v) rfl
      have rest := ih (c+1) (by omega) (by omega) v (by simpa [Nat.add_assoc] using hv)
      have whole := (round.append lift).append rest
      convert whole using 1
      simp only [Nat.add_assoc]
      nlinarith [unit]
/-- Prepared proof component for the unchanged live Cursor rows. Raw caller derives every cell premise. -/
theorem counted (k N B p S z n Q F : Nat) (T : Nat → Option Bool)
    (pos : 0 < p) (physical : p < S) (paid : 0 < Q) (room : S+z+n+3+Q < F)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b) (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none)
    (marks : ∀ i, S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap : ∀ i, S+z+n+3+Q < i → i < F → T i=none) (fence : T F=some false)
    (fresh : ∀ i, F < i → i ≤ F+(S-p)+2 → T i=none)
    (fit : F+(S-p)+2 < tapeLength N B) :
    (Cursor.machine k).run (2+(S-p)*(2*(F-p)+6))
      (⟨Cursor.q k 58,⟨p,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.rReady k,⟨S,by omega⟩,fun i => Target.image T F (S-p) i.val⟩ ∧
    (∀ u, u < 2+(S-p)*(2*(F-p)+6) →
      ((Cursor.machine k).run u (⟨Cursor.q k 58,⟨p,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)).state ≠ Cursor.rReady k) := by
  let r := S-p
  have fr : Frame T p S z n Q F r :=
    ⟨pos,physical,rfl,paid,room,source,eof,reg,sep,assn,right,marks,gap,fence,fresh⟩
  obtain ⟨b,hb⟩ := source p le_rfl physical
  have same := keep (Cursor.q k 58) (Cursor.q k 64) p p T .stay
    (by simp only [Cursor.q,small_mod k 58 (by omega)]; omega)
    (P := F+r+2) (by dsimp [r]; omega) (by dsimp [r]; omega)
    (by rw [hb]; exact (entry_rows k b).1) rfl
  have lift := hop (Cursor.q k 64) (Cursor.q k (base b)) p (p+1) T none .right
    (by simp only [Cursor.q,small_mod k 64 (by omega)]; omega)
    (P := F+r+2) (by dsimp [r]; omega) (by dsimp [r]; omega)
    (by rw [hb]; exact (entry_rows k b).2) rfl
  have rest := count_iteration k T p S z n Q F r fr r 0 (by dsimp [r]; omega) (by omega) b (by simpa using hb)
  have zeroImage : Target.image T F 0=T := by
    funext i; simp [Target.image,show ¬(F+2 ≤ i ∧ i < F+0+2) by omega]
  simp only [Nat.add_zero,zeroImage] at rest
  have path := (same.append lift).append rest
  have time : 1+1+r*(2*(F-p)+6)=2+(S-p)*(2*(F-p)+6) := rfl
  rw [time] at path
  refine ⟨path.execute fit,?_⟩
  intro u hu eq
  have before := path.first fit u hu
  dsimp only [embed] at before
  rw [eq] at before
  simp only [Cursor.rReady,Cursor.q,small_mod k 98 (by omega)] at before
  exact Nat.lt_irrefl 98 before
end SuffixCap
