import CappedWorkspace.Rows
namespace CappedWorkspace
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
  safe : c.state.val < 201
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
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hs : s.val < 201) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hs,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
/-- One exact public row that preserves the scanned symbol. -/
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hs : s.val < 201) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hs hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (hs : s.val < 201) (fit : h+r   ≤   P) (rows : ∀ i, h   ≤   i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right hs (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (hs : s.val < 201) (fit : low+r   ≤   P) (rows : ∀ i, low < i → i   ≤   low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left hs (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private theorem small_mod (k i : Nat) (h : i  ≤  201) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)

private theorem row_value (k i : Nat) (b : Option Bool) (lo : 98 ≤ i) (hi : i < 201) :
    let code := instructions[3*(i-98)+(match b with | none => 0 | some false => 1 | some true => 2)]!
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply setup_row k i _ b lo hi
  have len : instructions.length=309 := rfl
  have bound : 3*(i-98)+(match b with | none => 0 | some false => 1 | some true => 2) < instructions.length := by
    rw [len]; split <;> omega
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some]
  exact List.getElem?_eq_getElem bound
private theorem step_keep {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (mv : Move)
    (hs : 98 ≤ s) (ht : s < 201) (hb : h ≤ P) (ha : h' ≤ P)
    (row : (Cursor.machine k).step (Cursor.q k s) (T h)=(Cursor.q k d,T h,mv))
    (hm : dest h mv=h') : Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ :=
  keep _ _ _ _ _ _ (by simp only [Cursor.q,small_mod k s (by omega)]; exact ht) hb ha row hm
private theorem step_put {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (out : Option Bool) (mv : Move)
    (hs : 98 ≤ s) (ht : s < 201) (hb : h ≤ P) (ha : h' ≤ P)
    (row : (Cursor.machine k).step (Cursor.q k s) (T h)=(Cursor.q k d,out,mv))
    (hm : dest h mv=h') : Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',put T h out⟩ :=
  hop _ _ _ _ _ _ _ (by simp only [Cursor.q,small_mod k s (by omega)]; exact ht) hb ha row hm
private def nimage (C : Nat → Option Bool) (L n D c : Nat) : Nat → Option Bool := fun i =>
  if L+n+1-c ≤ i ∧ i < L+n+1 then some true else
  if D < i ∧ i ≤ D+c then some false else C i
private structure NFrame (C : Nat → Option Bool) (L n Q F r : Nat) : Prop where
  paid : 0 < Q
  room : L+n+1+Q < F
  sep : C L=none
  assn : ∀ i, L < i → i < L+n+1 → C i=some false
  right : C (L+n+1)=none
  marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → C i=some true
  gap : ∀ i, L+n+1+Q < i → i < F → C i=none
  fence : C F=some false
  d0 : C (F+1)=none
  bank0 : ∀ i, F+1 < i → i < F+r+2 → C i=some true
  fresh : ∀ i, F+r+2 ≤ i → i ≤ F+5*r+n+7 → C i=none
private theorem n_round (k : Nat) (C : Nat → Option Bool) (L n Q F r c : Nat)
    (fr : NFrame C L n Q F r) (hc : c < n) :
    Path k (F+5*r+n+7) (2*(F-(L+n+1))+2*r+4*c+13)
      ⟨Cursor.q k 101,L+n+1,nimage C L n (F+r+2) c⟩
      ⟨Cursor.q k 101,L+n+1,nimage C L n (F+r+2) (c+1)⟩ := by
  let H := L+n+1
  let D := F+r+2
  let P := F+5*r+n+7
  let T := nimage C L n D c
  let V := put T (H-c-1) (some true)
  let E := nimage C L n D (c+1)
  have room := fr.room
  have paid := fr.paid
  have old (i : Nat) (hi : i < H-c ∨ H ≤ i) (hb : i ≤ D ∨ D+c < i) : T i=C i := by
    simp only [T,nimage]
    rw [if_neg (by omega),if_neg (by omega)]
  have mark (i : Nat) (lo : H-c ≤ i) (hi : i < H) : T i=some true := by
    simp only [T,nimage]; rw [if_pos ⟨lo,hi⟩]
  have oldV (i : Nat) (ne : i ≠ H-c-1) (hi : i < H-c ∨ H ≤ i) (hb : i ≤ D ∨ D+c < i) : V i=C i := by
    simp only [V,put,ne,↓reduceIte,old i hi hb]
  have markedV (i : Nat) (lo : H-c-1 ≤ i) (hi : i < H) : V i=some true := by
    by_cases he : i=H-c-1
    · simp [V,put,he]
    · simp only [V,put,he,↓reduceIte]; exact mark i (by omega) hi
  have append : put V (D+c+1) (some false)=E := by
    funext i
    dsimp [V,T,E,nimage,put,H,D]
    split_ifs <;> first | rfl | omega
  have a := step_keep (k := k) (P := P) 101 102 (H) (H-1) T .left (by omega) (by omega) (by omega) (by omega)
    (by have bit : T (H)=none := by rw [old _ (by omega) (by omega)]; exact fr.right
        rw [bit]; exact row_value k 101 none (by omega) (by omega)) rfl
  have b := sweepL (Cursor.q k 102) T (H-c-1) (c)
    (by simp only [Cursor.q,small_mod k 102 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : T i=some true := by exact mark i (by omega) (by omega)
      rw [bit]; exact row_value k 102 (some true) (by omega) (by omega))
  rw [show H-c-1+c=H-1 by omega] at b
  have c0 := step_put (k := k) (P := P) 102 103 (H-c-1) (H-c) T (some true) .right (by omega) (by omega) (by omega) (by omega)
    (by have bit : T (H-c-1)=some false := by rw [old _ (by omega) (by omega)]; exact fr.assn _ (by omega) (by omega)
        rw [bit]; exact row_value k 102 (some false) (by omega) (by omega)) (by change H-c-1+1=H-c; omega)
  have d := sweepR (Cursor.q k 103) V (H-c) (c)
    (by simp only [Cursor.q,small_mod k 103 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : V i=some true := by exact markedV i (by omega) (by omega)
      rw [bit]; exact row_value k 103 (some true) (by omega) (by omega))
  rw [show H-c+c=H by omega] at d
  have e := step_keep (k := k) (P := P) 103 104 (H) (H) V .stay (by omega) (by omega) (by omega) (by omega)
    (by have bit : V (H)=none := by rw [oldV _ (by omega) (by omega) (by omega)]; exact fr.right
        rw [bit]; exact row_value k 103 none (by omega) (by omega)) rfl
  have f := step_keep (k := k) (P := P) 104 105 (H) (H+1) V .right (by omega) (by omega) (by omega) (by omega)
    (by have bit : V (H)=none := by rw [oldV _ (by omega) (by omega) (by omega)]; exact fr.right
        rw [bit]; exact row_value k 104 none (by omega) (by omega)) rfl
  have g := sweepR (Cursor.q k 105) V (H+1) (F-H-1)
    (by simp only [Cursor.q,small_mod k 105 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi
      rw [oldV _ (by omega) (by omega) (by omega)]
      by_cases hm : i ≤ H+Q
      · rw [fr.marks i (by omega) hm]; exact row_value k 105 (some true) (by omega) (by omega)
      · rw [fr.gap i (by omega) (by omega)]; exact row_value k 105 none (by omega) (by omega))
  rw [show H+1+(F-H-1)=F by omega] at g
  have h := step_keep (k := k) (P := P) 105 106 (F) (F+1) V .right (by omega) (by omega) (by omega) (by omega)
    (by have bit : V (F)=some false := by rw [oldV _ (by omega) (by omega) (by omega)]; exact fr.fence
        rw [bit]; exact row_value k 105 (some false) (by omega) (by omega)) rfl
  have i0 := step_keep (k := k) (P := P) 106 107 (F+1) (F+2) V .right (by omega) (by omega) (by omega) (by omega)
    (by have bit : V (F+1)=none := by rw [oldV _ (by omega) (by omega) (by omega)]; exact fr.d0
        rw [bit]; exact row_value k 106 none (by omega) (by omega)) rfl
  have j := sweepR (Cursor.q k 107) V (F+2) (r)
    (by simp only [Cursor.q,small_mod k 107 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : V i=some true := by rw [oldV _ (by omega) (by omega) (by omega)]; exact fr.bank0 i (by omega) (by omega)
      rw [bit]; exact row_value k 107 (some true) (by omega) (by omega))
  rw [show F+2+r=D by omega] at j
  have l := step_keep (k := k) (P := P) 107 108 (D) (D) V .stay (by omega) (by omega) (by omega) (by omega)
    (by have bit : V (D)=none := by rw [oldV _ (by omega) (by omega) (by omega)]; (apply fr.fresh <;> omega)
        rw [bit]; exact row_value k 107 none (by omega) (by omega)) rfl
  have m := step_keep (k := k) (P := P) 108 109 (D) (D+1) V .right (by omega) (by omega) (by omega) (by omega)
    (by have bit : V (D)=none := by rw [oldV _ (by omega) (by omega) (by omega)]; (apply fr.fresh <;> omega)
        rw [bit]; exact row_value k 108 none (by omega) (by omega)) rfl
  have n0 := sweepR (Cursor.q k 109) V (D+1) (c)
    (by simp only [Cursor.q,small_mod k 109 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : V i=some false := by simp only [V,put,show i ≠ H-c-1 by omega,↓reduceIte,T,nimage]; rw [if_neg (by omega),if_pos (by omega)]
      rw [bit]; exact row_value k 109 (some false) (by omega) (by omega))
  rw [show D+1+c=D+c+1 by omega] at n0
  have o := step_put (k := k) (P := P) 109 110 (D+c+1) (D+c) V (some false) .left (by omega) (by omega) (by omega) (by omega)
    (by have bit : V (D+c+1)=none := by rw [oldV _ (by omega) (by omega) (by omega)]; (apply fr.fresh <;> omega)
        rw [bit]; exact row_value k 109 none (by omega) (by omega)) rfl
  rw [append] at o
  have oldE (i : Nat) (hi : i < H-(c+1) ∨ H ≤ i) (hb : i ≤ D ∨ D+(c+1) < i) : E i=C i := by
    simp only [E,nimage]
    rw [if_neg (by omega),if_neg (by omega)]
  have p0 := sweepL (Cursor.q k 110) E (D) (c)
    (by simp only [Cursor.q,small_mod k 110 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : E i=some false := by simp only [E,nimage]; rw [if_neg (by omega),if_pos (by omega)]
      rw [bit]; exact row_value k 110 (some false) (by omega) (by omega))
  have p1 := step_keep (k := k) (P := P) 110 111 (D) (D) E .stay (by omega) (by omega) (by omega) (by omega)
    (by have bit : E (D)=none := by rw [oldE _ (by omega) (by omega)]; (apply fr.fresh <;> omega)
        rw [bit]; exact row_value k 110 none (by omega) (by omega)) rfl
  have p2 := step_keep (k := k) (P := P) 111 112 (D) (D-1) E .left (by omega) (by omega) (by omega) (by omega)
    (by have bit : E (D)=none := by rw [oldE _ (by omega) (by omega)]; (apply fr.fresh <;> omega)
        rw [bit]; exact row_value k 111 none (by omega) (by omega)) rfl
  have p3 := sweepL (Cursor.q k 112) E (F+1) (r)
    (by simp only [Cursor.q,small_mod k 112 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : E i=some true := by rw [oldE _ (by omega) (by omega)]; (apply fr.bank0 <;> omega)
      rw [bit]; exact row_value k 112 (some true) (by omega) (by omega))
  rw [show F+1+r=D-1 by omega] at p3
  have p4 := step_keep (k := k) (P := P) 112 113 (F+1) (F+1) E .stay (by omega) (by omega) (by omega) (by omega)
    (by have bit : E (F+1)=none := by rw [oldE _ (by omega) (by omega)]; exact fr.d0
        rw [bit]; exact row_value k 112 none (by omega) (by omega)) rfl
  have p5 := step_keep (k := k) (P := P) 113 114 (F+1) (F) E .left (by omega) (by omega) (by omega) (by omega)
    (by have bit : E (F+1)=none := by rw [oldE _ (by omega) (by omega)]; exact fr.d0
        rw [bit]; exact row_value k 113 none (by omega) (by omega)) rfl
  have p6 := step_keep (k := k) (P := P) 114 115 (F) (F-1) E .left (by omega) (by omega) (by omega) (by omega)
    (by have bit : E (F)=some false := by rw [oldE _ (by omega) (by omega)]; exact fr.fence
        rw [bit]; exact row_value k 114 (some false) (by omega) (by omega)) rfl
  have p7 := sweepL (Cursor.q k 115) E (H+Q) (F-H-Q-1)
    (by simp only [Cursor.q,small_mod k 115 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : E i=none := by rw [oldE _ (by omega) (by omega)]; exact fr.gap _ (by omega) (by omega)
      rw [bit]; exact row_value k 115 none (by omega) (by omega))
  rw [show H+Q+(F-H-Q-1)=F-1 by omega] at p7
  have p8 := step_keep (k := k) (P := P) 115 116 (H+Q) (H+Q-1) E .left (by omega) (by omega) (by omega) (by omega)
    (by have bit : E (H+Q)=some true := by rw [oldE _ (by omega) (by omega)]; exact fr.marks _ (by omega) (by omega)
        rw [bit]; exact row_value k 115 (some true) (by omega) (by omega)) rfl
  have p9 := sweepL (Cursor.q k 116) E (H) (Q-1)
    (by simp only [Cursor.q,small_mod k 116 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; have bit : E i=some true := by rw [oldE _ (by omega) (by omega)]; exact fr.marks _ (by omega) (by omega)
      rw [bit]; exact row_value k 116 (some true) (by omega) (by omega))
  rw [show H+(Q-1)=H+Q-1 by omega] at p9
  have p10 := step_keep (k := k) (P := P) 116 101 (H) (H) E .stay (by omega) (by omega) (by omega) (by omega)
    (by have bit : E (H)=none := by rw [oldE _ (by omega) (by omega)]; exact fr.right
        rw [bit]; exact row_value k 116 none (by omega) (by omega)) rfl
  have path := a |>.append b |>.append c0 |>.append d |>.append e |>.append f |>.append g |>.append h |>.append i0 |>.append j |>.append l |>.append m |>.append n0 |>.append o |>.append p0 |>.append p1 |>.append p2 |>.append p3 |>.append p4 |>.append p5 |>.append p6 |>.append p7 |>.append p8 |>.append p9 |>.append p10
  convert path using 1
  dsimp only [H,D,P,T,V,E] at *
  omega
private theorem n_iteration (k : Nat) (C : Nat → Option Bool) (L n Q F r d c : Nat)
    (fr : NFrame C L n Q F r) (hc : c+d=n) :
    ∃ t, t ≤ d*(2*(F-(L+n+1))+2*r+4*n+13) ∧
      Path k (F+5*r+n+7) t ⟨Cursor.q k 101,L+n+1,nimage C L n (F+r+2) c⟩
        ⟨Cursor.q k 101,L+n+1,nimage C L n (F+r+2) n⟩ := by
  induction d generalizing c with
  | zero =>
    have eq : c=n := by omega
    subst c
    exact ⟨0,by omega,Path.nil _ (by change L+n+1 ≤ F+5*r+n+7; have := fr.room; omega)⟩
  | succ d ih =>
    have one := n_round k C L n Q F r c fr (by omega)
    obtain ⟨t,ht,rest⟩ := ih (c+1) (by omega)
    refine ⟨_,?_,one.append rest⟩
    have mul := Nat.mul_le_mul_left 4 (show c ≤ n by omega)
    nlinarith
private theorem n_zero (C : Nat → Option Bool) (L n D : Nat) : nimage C L n D 0=C := by
  funext i; simp only [nimage,Nat.sub_zero,Nat.add_zero]
  rw [if_neg (by omega),if_neg (by omega)]
private theorem n_finish (k : Nat) (C : Nat → Option Bool) (L n Q F r : Nat)
    (fr : NFrame C L n Q F r) :
    Path k (F+5*r+n+7) (2*n+(F-(L+n+1))+5)
      ⟨Cursor.q k 101,L+n+1,nimage C L n (F+r+2) n⟩
      ⟨Cursor.q k 121,F+1,nimage C L n (F+r+2) n⟩ := by
  let H := L+n+1
  let D := F+r+2
  let P := F+5*r+n+7
  let E := nimage C L n D n
  have room := fr.room
  have old (i : Nat) (hi : i ≤ L ∨ H ≤ i) (hb : i ≤ D ∨ D+n < i) : E i=C i := by
    simp only [E,nimage]
    rw [if_neg (by omega),if_neg (by omega)]
  have marked (i : Nat) (lo : L < i) (hi : i < H) : E i=some true := by
    simp only [E,nimage]; rw [if_pos (by omega)]
  have a := step_keep (k := k) (P := P) 101 102 H (H-1) E .left (by omega) (by omega) (by omega) (by omega)
    (by rw [old _ (by omega) (by omega),fr.right]; exact row_value k 101 none (by omega) (by omega)) rfl
  have b := sweepL (Cursor.q k 102) E L n
    (by simp only [Cursor.q,small_mod k 102 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [marked i lo (by omega)]; exact row_value k 102 (some true) (by omega) (by omega))
  rw [show L+n=H-1 by omega] at b
  have c := step_keep (k := k) (P := P) 102 117 L (L+1) E .right (by omega) (by omega) (by omega) (by omega)
    (by rw [old _ (by omega) (by omega),fr.sep]; exact row_value k 102 none (by omega) (by omega)) rfl
  have d := sweepR (Cursor.q k 117) E (L+1) n
    (by simp only [Cursor.q,small_mod k 117 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [marked i (by omega) (by omega)]; exact row_value k 117 (some true) (by omega) (by omega))
  rw [show L+1+n=H by omega] at d
  have e := step_keep (k := k) (P := P) 117 118 H H E .stay (by omega) (by omega) (by omega) (by omega)
    (by rw [old _ (by omega) (by omega),fr.right]; exact row_value k 117 none (by omega) (by omega)) rfl
  have f := step_keep (k := k) (P := P) 118 119 H (H+1) E .right (by omega) (by omega) (by omega) (by omega)
    (by rw [old _ (by omega) (by omega),fr.right]; exact row_value k 118 none (by omega) (by omega)) rfl
  have g := sweepR (Cursor.q k 119) E (H+1) (F-H-1)
    (by simp only [Cursor.q,small_mod k 119 (by omega)]; omega) (P := P) (by omega) (by
      intro i lo hi; rw [old _ (by omega) (by omega)]
      by_cases hm : i ≤ H+Q
      · rw [fr.marks i (by omega) hm]; exact row_value k 119 (some true) (by omega) (by omega)
      · rw [fr.gap i (by omega) (by omega)]; exact row_value k 119 none (by omega) (by omega))
  rw [show H+1+(F-H-1)=F by omega] at g
  have h := step_keep (k := k) (P := P) 119 120 F (F+1) E .right (by omega) (by omega) (by omega) (by omega)
    (by rw [old _ (by omega) (by omega),fr.fence]; exact row_value k 119 (some false) (by omega) (by omega)) rfl
  have i := step_keep (k := k) (P := P) 120 121 (F+1) (F+1) E .stay (by omega) (by omega) (by omega) (by omega)
    (by rw [old _ (by omega) (by omega),fr.d0]; exact row_value k 120 none (by omega) (by omega)) rfl
  have path := a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h |>.append i
  convert path using 1
  dsimp only [H,D,P,E] at *
  omega
private theorem crossR (k P s count : Nat) (D : Nat → Nat) (T : Nat → Option Bool)
    (fit : ∀ i, i ≤ count → D i ≤ P) (ordered : ∀ i, i < count → D i < D (i+1))
    (empty : ∀ i, i ≤ count → T (D i)=none)
    (filled : ∀ j, j < count → ∀ i, D j < i → i < D (j+1) → ∃ b, T i=some b)
    (safe : ∀ i, i < count → 98 ≤ s+2*i ∧ s+2*i+1 < 201)
    (enter : ∀ i, i < count → ∀ b, (Cursor.machine k).step (Cursor.q k (s+2*i)) b=(Cursor.q k (s+2*i+1),b,.right))
    (scan : ∀ i, i < count → ∀ b, (Cursor.machine k).step (Cursor.q k (s+2*i+1)) (some b)=(Cursor.q k (s+2*i+1),some b,.right))
    (leave : ∀ i, i < count → (Cursor.machine k).step (Cursor.q k (s+2*i+1)) none=(Cursor.q k (s+2*i+2),none,.stay)) :
    ∃ t, t ≤ count*(P+2) ∧ Path k P t ⟨Cursor.q k s,D 0,T⟩ ⟨Cursor.q k (s+2*count),D count,T⟩ := by
  induction count generalizing s D with
  | zero => exact ⟨0,by omega,by simpa using Path.nil ⟨Cursor.q k s,D 0,T⟩ (fit 0 le_rfl)⟩
  | succ c ih =>
    have ord : D 0 < D 1 := ordered 0 (by omega)
    have sf : 98 ≤ s ∧ s+1 < 201 := by simpa using safe 0 (by omega)
    have fit0 := fit 0 (by omega)
    have dfit := fit 1 (by omega)
    have a := step_keep (k := k) (P := P) s (s+1) (D 0) (D 0+1) T .right
      (by simpa using sf.1) (by omega) (by omega) (by omega) (by simpa using enter 0 (by omega) (T (D 0))) rfl
    have b := sweepR (Cursor.q k (s+1)) T (D 0+1) (D 1-D 0-1)
      (by simp only [Cursor.q,small_mod k (s+1) (by omega)]; simpa using sf.2) (P := P) (by omega) (by
        intro i lo hi; have ff : ∀ i, D 0 < i → i < D 1 → ∃ b, T i=some b := filled 0 (by omega)
        obtain ⟨v,hv⟩ := ff i (by omega) (by omega)
        rw [hv]; simpa using scan 0 (by omega) v)
    rw [show D 0+1+(D 1-D 0-1)=D 1 by omega] at b
    have e := step_keep (k := k) (P := P) (s+1) (s+2) (D 1) (D 1) T .stay
      (by omega) (by omega) dfit dfit (by rw [empty 1 (by omega)]; simpa using leave 0 (by omega)) rfl
    obtain ⟨t,ht,rest⟩ := ih (s+2) (fun i => D (i+1))
      (by intro i hi; exact fit (i+1) (by omega))
      (by intro i hi; simpa [Nat.add_assoc] using ordered (i+1) (by omega))
      (by intro i hi; exact empty (i+1) (by omega))
      (by intro j hj i lo hi; simpa [Nat.add_assoc] using filled (j+1) (by omega) i lo hi)
      (by intro i hi; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using safe (i+1) (by omega))
      (by intro i hi v; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using enter (i+1) (by omega) v)
      (by intro i hi v; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using scan (i+1) (by omega) v)
      (by intro i hi; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using leave (i+1) (by omega))
    have path := a.append b |>.append e |>.append rest
    refine ⟨1+(D 1-D 0-1)+1+t,?_,?_⟩
    · have width : D 1-D 0-1 ≤ P := (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans dfit)
      nlinarith
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem crossL (k P s count : Nat) (D : Nat → Nat) (T : Nat → Option Bool)
    (fit : ∀ i, i ≤ count → D i ≤ P) (ordered : ∀ i, i < count → D (i+1) < D i)
    (empty : ∀ i, i ≤ count → T (D i)=none)
    (filled : ∀ j, j < count → ∀ i, D (j+1) < i → i < D j → ∃ b, T i=some b)
    (safe : ∀ i, i < count → 98 ≤ s+2*i ∧ s+2*i+1 < 201)
    (enter : ∀ i, i < count → ∀ b, (Cursor.machine k).step (Cursor.q k (s+2*i)) b=(Cursor.q k (s+2*i+1),b,.left))
    (scan : ∀ i, i < count → ∀ b, (Cursor.machine k).step (Cursor.q k (s+2*i+1)) (some b)=(Cursor.q k (s+2*i+1),some b,.left))
    (leave : ∀ i, i < count → (Cursor.machine k).step (Cursor.q k (s+2*i+1)) none=(Cursor.q k (s+2*i+2),none,.stay)) :
    ∃ t, t ≤ count*(P+2) ∧ Path k P t ⟨Cursor.q k s,D 0,T⟩ ⟨Cursor.q k (s+2*count),D count,T⟩ := by
  induction count generalizing s D with
  | zero => exact ⟨0,by omega,by simpa using Path.nil ⟨Cursor.q k s,D 0,T⟩ (fit 0 le_rfl)⟩
  | succ c ih =>
    have ord : D 1 < D 0 := ordered 0 (by omega)
    have sf : 98 ≤ s ∧ s+1 < 201 := by simpa using safe 0 (by omega)
    have fit0 := fit 0 (by omega)
    have dfit := fit 1 (by omega)
    have a := step_keep (k := k) (P := P) s (s+1) (D 0) (D 0-1) T .left
      (by simpa using sf.1) (by omega) (by omega) (by omega) (by simpa using enter 0 (by omega) (T (D 0))) (by simp [dest])
    have b := sweepL (Cursor.q k (s+1)) T (D 1) (D 0-D 1-1)
      (by simp only [Cursor.q,small_mod k (s+1) (by omega)]; simpa using sf.2) (P := P) (by omega) (by
        intro i lo hi; have ff : ∀ i, D 1 < i → i < D 0 → ∃ b, T i=some b := filled 0 (by omega)
        obtain ⟨v,hv⟩ := ff i (by omega) (by omega)
        rw [hv]; simpa using scan 0 (by omega) v)
    rw [show D 1+(D 0-D 1-1)=D 0-1 by omega] at b
    have e := step_keep (k := k) (P := P) (s+1) (s+2) (D 1) (D 1) T .stay
      (by omega) (by omega) dfit dfit (by rw [empty 1 (by omega)]; simpa using leave 0 (by omega)) rfl
    obtain ⟨t,ht,rest⟩ := ih (s+2) (fun i => D (i+1))
      (by intro i hi; exact fit (i+1) (by omega))
      (by intro i hi; simpa [Nat.add_assoc] using ordered (i+1) (by omega))
      (by intro i hi; exact empty (i+1) (by omega))
      (by intro j hj i lo hi; simpa [Nat.add_assoc] using filled (j+1) (by omega) i lo hi)
      (by intro i hi; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using safe (i+1) (by omega))
      (by intro i hi v; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using enter (i+1) (by omega) v)
      (by intro i hi v; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using scan (i+1) (by omega) v)
      (by intro i hi; simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using leave (i+1) (by omega))
    have path := a.append b |>.append e |>.append rest
    refine ⟨1+(D 0-D 1-1)+1+t,?_,?_⟩
    · have width : D 0-D 1-1 ≤ P := (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (fit 0 (by omega)))
      nlinarith
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private def copyBase (j : Nat) : Nat := 121+12*j+2*j*j
private structure CopyRows (k j s : Nat) : Prop where
  start : ∀ b, (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k (s+1),b,.right)
  lift : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+2),none,.right)
  stop : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+13+4*j),none,.left)
  tail : ∀ b, (Cursor.machine k).step (Cursor.q k (s+2)) (some b)=(Cursor.q k (s+2),some b,.right)
  tailEnd : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k (s+3),none,.stay)
  outEnter : ∀ i, i ≤ j → ∀ b, (Cursor.machine k).step (Cursor.q k (s+3+2*i)) b=(Cursor.q k (s+3+2*i+1),b,.right)
  outScan : ∀ i, i ≤ j → ∀ b, (Cursor.machine k).step (Cursor.q k (s+3+2*i+1)) (some b)=(Cursor.q k (s+3+2*i+1),some b,.right)
  outEnd : ∀ i, i ≤ j → (Cursor.machine k).step (Cursor.q k (s+3+2*i+1)) none=(Cursor.q k (s+3+2*i+2),none,.stay)
  write : ∀ b, (Cursor.machine k).step (Cursor.q k (s+5+2*j)) b=(Cursor.q k (s+6+2*j),b,.right)
  appendScan : ∀ b, (Cursor.machine k).step (Cursor.q k (s+6+2*j)) (some b)=(Cursor.q k (s+6+2*j),some b,.right)
  appendEnd : (Cursor.machine k).step (Cursor.q k (s+6+2*j)) none=(Cursor.q k (s+7+2*j),none,.stay)
  put : (Cursor.machine k).step (Cursor.q k (s+7+2*j)) none=(Cursor.q k (s+8+2*j),some false,.left)
  ret : ∀ b, (Cursor.machine k).step (Cursor.q k (s+8+2*j)) (some b)=(Cursor.q k (s+8+2*j),some b,.left)
  retEnd : (Cursor.machine k).step (Cursor.q k (s+8+2*j)) none=(Cursor.q k (s+9+2*j),none,.stay)
  inEnter : ∀ i, i ≤ j → ∀ b, (Cursor.machine k).step (Cursor.q k (s+9+2*j+2*i)) b=(Cursor.q k (s+9+2*j+2*i+1),b,.left)
  inScan : ∀ i, i ≤ j → ∀ b, (Cursor.machine k).step (Cursor.q k (s+9+2*j+2*i+1)) (some b)=(Cursor.q k (s+9+2*j+2*i+1),some b,.left)
  inEnd : ∀ i, i ≤ j → (Cursor.machine k).step (Cursor.q k (s+9+2*j+2*i+1)) none=(Cursor.q k (s+9+2*j+2*i+2),none,.stay)
  hole : ∀ b, (Cursor.machine k).step (Cursor.q k (s+11+4*j)) b=(Cursor.q k (s+12+4*j),b,.left)
  seek : ∀ b, (Cursor.machine k).step (Cursor.q k (s+12+4*j)) (some b)=(Cursor.q k (s+12+4*j),some b,.left)
  restore : (Cursor.machine k).step (Cursor.q k (s+12+4*j)) none=(Cursor.q k (s+1),some true,.right)
  doneScan : ∀ b, (Cursor.machine k).step (Cursor.q k (s+13+4*j)) (some b)=(Cursor.q k (s+13+4*j),some b,.left)
  doneEnd : (Cursor.machine k).step (Cursor.q k (s+13+4*j)) none=(Cursor.q k (s+14+4*j),none,.stay)
private theorem copy_safe (j i : Nat) (hj : j ≤ 3) (hi : i ≤ 13+4*j) :
    98 ≤ copyBase j+i ∧ copyBase j+i < 201 := by
  dsimp only [copyBase]
  interval_cases j <;> omega
private theorem copy_rows (k j : Nat) (hj : j ≤ 3) : CopyRows k j (copyBase j) := by
  constructor
  · intro b; have sf := copy_safe j (0) hj (by omega); have h := row_value k (copyBase j) b (by omega) (by omega); interval_cases j; all_goals (cases b with | none => exact h | some b => cases b <;> exact h)
  · have sf := copy_safe j (1) hj (by omega); have h := row_value k (copyBase j+1) (some true) (by omega) (by omega); interval_cases j; all_goals exact h
  · have sf := copy_safe j (1) hj (by omega); have h := row_value k (copyBase j+1) none (by omega) (by omega); interval_cases j; all_goals exact h
  · intro b; have sf := copy_safe j (2) hj (by omega); have h := row_value k (copyBase j+2) (some b) (by omega) (by omega); interval_cases j; all_goals cases b <;> exact h
  · have sf := copy_safe j (2) hj (by omega); have h := row_value k (copyBase j+2) none (by omega) (by omega); interval_cases j; all_goals exact h
  · intro i hi b; have sf := copy_safe j (3+2*i) hj (by omega); have h := row_value k (copyBase j+3+2*i) b (by omega) (by omega); interval_cases j <;> interval_cases i; all_goals (cases b with | none => exact h | some b => cases b <;> exact h)
  · intro i hi b; have sf := copy_safe j (3+2*i+1) hj (by omega); have h := row_value k (copyBase j+3+2*i+1) (some b) (by omega) (by omega); interval_cases j <;> interval_cases i; all_goals cases b <;> exact h
  · intro i hi; have sf := copy_safe j (3+2*i+1) hj (by omega); have h := row_value k (copyBase j+3+2*i+1) none (by omega) (by omega); interval_cases j <;> interval_cases i; all_goals exact h
  · intro b; have sf := copy_safe j (5+2*j) hj (by omega); have h := row_value k (copyBase j+5+2*j) b (by omega) (by omega); interval_cases j; all_goals (cases b with | none => exact h | some b => cases b <;> exact h)
  · intro b; have sf := copy_safe j (6+2*j) hj (by omega); have h := row_value k (copyBase j+6+2*j) (some b) (by omega) (by omega); interval_cases j; all_goals cases b <;> exact h
  · have sf := copy_safe j (6+2*j) hj (by omega); have h := row_value k (copyBase j+6+2*j) none (by omega) (by omega); interval_cases j; all_goals exact h
  · have sf := copy_safe j (7+2*j) hj (by omega); have h := row_value k (copyBase j+7+2*j) none (by omega) (by omega); interval_cases j; all_goals exact h
  · intro b; have sf := copy_safe j (8+2*j) hj (by omega); have h := row_value k (copyBase j+8+2*j) (some b) (by omega) (by omega); interval_cases j; all_goals cases b <;> exact h
  · have sf := copy_safe j (8+2*j) hj (by omega); have h := row_value k (copyBase j+8+2*j) none (by omega) (by omega); interval_cases j; all_goals exact h
  · intro i hi b; have sf := copy_safe j (9+2*j+2*i) hj (by omega); have h := row_value k (copyBase j+9+2*j+2*i) b (by omega) (by omega); interval_cases j <;> interval_cases i; all_goals (cases b with | none => exact h | some b => cases b <;> exact h)
  · intro i hi b; have sf := copy_safe j (9+2*j+2*i+1) hj (by omega); have h := row_value k (copyBase j+9+2*j+2*i+1) (some b) (by omega) (by omega); interval_cases j <;> interval_cases i; all_goals cases b <;> exact h
  · intro i hi; have sf := copy_safe j (9+2*j+2*i+1) hj (by omega); have h := row_value k (copyBase j+9+2*j+2*i+1) none (by omega) (by omega); interval_cases j <;> interval_cases i; all_goals exact h
  · intro b; have sf := copy_safe j (11+4*j) hj (by omega); have h := row_value k (copyBase j+11+4*j) b (by omega) (by omega); interval_cases j; all_goals (cases b with | none => exact h | some b => cases b <;> exact h)
  · intro b; have sf := copy_safe j (12+4*j) hj (by omega); have h := row_value k (copyBase j+12+4*j) (some b) (by omega) (by omega); interval_cases j; all_goals cases b <;> exact h
  · have sf := copy_safe j (12+4*j) hj (by omega); have h := row_value k (copyBase j+12+4*j) none (by omega) (by omega); interval_cases j; all_goals exact h
  · intro b; have sf := copy_safe j (13+4*j) hj (by omega); have h := row_value k (copyBase j+13+4*j) (some b) (by omega) (by omega); interval_cases j; all_goals cases b <;> exact h
  · have sf := copy_safe j (13+4*j) hj (by omega); have h := row_value k (copyBase j+13+4*j) none (by omega) (by omega); interval_cases j; all_goals exact h
private def fill (C : Nat → Option Bool) (D c : Nat) : Nat → Option Bool := fun i =>
  if D < i ∧ i ≤ D+c then some false else C i
private structure CopyFrame (C : Nat → Option Bool) (P d r j : Nat) (D : Nat → Nat) : Prop where
  anchor : D 0=d+r+1
  fit : ∀ i, i ≤ j+1 → D i+r+1 ≤ P
  after : ∀ i, i ≤ j+1 → d+r+1 ≤ D i
  ordered : ∀ i, i ≤ j → D i < D (i+1)
  empty : ∀ i, i ≤ j+1 → C (D i)=none
  filled : ∀ h, h ≤ j → ∀ i, D h < i → i < D (h+1) → ∃ b, C i=some b
  left : C d=none
  bits : ∀ i, d < i → i < d+r+1 → C i=some true
  fresh : ∀ i, D (j+1) ≤ i → i ≤ D (j+1)+r+1 → C i=none
private theorem fill_old (C : Nat → Option Bool) (D c i : Nat) (hi : i ≤ D ∨ D+c < i) :
    fill C D c i=C i := by rw [fill,if_neg (by omega)]
private theorem fill_zero (C : Nat → Option Bool) (D : Nat) : fill C D 0=C := by
  funext i; exact fill_old C D 0 i (by omega)
private theorem clone_round (k P d r j c : Nat) (D : Nat → Nat) (C : Nat → Option Bool)
    (hj : j ≤ 3) (hc : c < r) (fr : CopyFrame C P d r j D) :
    ∃ t, t ≤ 16*(P+2) ∧ Path k P t
      ⟨Cursor.q k (copyBase j+1),d+c+1,fill C (D (j+1)) c⟩
      ⟨Cursor.q k (copyBase j+1),d+c+2,fill C (D (j+1)) (c+1)⟩ := by
  let s := copyBase j
  let h := d+c+1
  let Z := D (j+1)
  let B := fill C Z c
  let T := put B h none
  let E := fill C Z (c+1)
  let V := put E h none
  have rows := copy_rows k j hj
  have fit := fr.fit (j+1) le_rfl
  have after := fr.after (j+1) le_rfl
  have anchor := fr.anchor
  have safe (i : Nat) (hi : i ≤ 13+4*j) : 98 ≤ s+i ∧ s+i < 201 := by
    dsimp only [s,copyBase]
    interval_cases j <;> omega
  have startLow : 98 ≤ s := (safe 0 (by omega)).1
  have oldB (i : Nat) (hi : i ≤ Z) : B i=C i := fill_old C Z c i (Or.inl hi)
  have oldT (i : Nat) (hi : i ≤ Z) (ne : i ≠ h) : T i=C i := by
    simp only [T,put,ne,↓reduceIte,oldB i hi]
  have oldV (i : Nat) (hi : i ≤ Z) (ne : i ≠ h) : V i=C i := by
    simp only [V,put,ne,↓reduceIte,E,fill_old C Z (c+1) i (Or.inl hi)]
  have low (i : Nat) (hi : i ≤ j+1) : d+r+1 ≤ D i := fr.after i hi
  have upper (i : Nat) (hi : i ≤ j+1) : D i ≤ Z := by
    have mono : ∀ a b, a ≤ b → b ≤ j+1 → D a ≤ D b := by
      intro a b hab hb
      induction b with
      | zero => simpa only [show a=0 by omega] using (Nat.le_refl (D 0))
      | succ b ih =>
        by_cases eq : a=b+1
        · subst a; rfl
        · exact (ih (by omega) (by omega)).trans (Nat.le_of_lt (fr.ordered b (by omega)))
    exact mono i (j+1) hi le_rfl
  have add : put T (Z+c+1) (some false)=V := by
    funext i
    dsimp only [T,B,V,E,fill,put]
    split_ifs <;> first | rfl | omega
  have restore : put V h (some true)=E := by
    have bit : E h=some true := by
      dsimp only [E]
      rw [fill_old C Z (c+1) h (Or.inl (by omega))]
      exact fr.bits h (by omega) (by omega)
    funext i; by_cases hi : i=h
    · subst i; simp [put,bit]
    · simp [V,put,hi]
  have a := step_put (k := k) (P := P) (s+1) (s+2) h (h+1) B none .right
    (by have hv := safe 1 (by omega); omega) (by have hv := safe 1 (by omega); omega) (by omega) (by omega)
    (by rw [oldB h (by omega),fr.bits h (by omega) (by omega)]; exact rows.lift) rfl
  have b := sweepR (Cursor.q k (s+2)) T (h+1) (r-c-1)
    (by simp only [Cursor.q,small_mod k (s+2) (by have := safe 2 (by omega); omega)]; exact (by have hv := safe 2 (by omega); omega))
    (P := P) (by omega) (by intro i lo hi; rw [oldT _ (by omega) (by omega),fr.bits _ (by omega) (by omega)]; exact rows.tail true)
  rw [show h+1+(r-c-1)=D 0 by omega] at b
  have e := step_keep (k := k) (P := P) (s+2) (s+3) (D 0) (D 0) T .stay
    (by have hv := safe 2 (by omega); omega) (by have hv := safe 2 (by omega); omega) (by have := fr.fit 0 (by omega); omega) (by have := fr.fit 0 (by omega); omega)
    (by rw [oldT _ (upper 0 (by omega)) (by omega),fr.empty 0 (by omega)]; exact rows.tailEnd) rfl
  obtain ⟨outTime,hto,out⟩ := crossR k P (s+3) (j+1) D T
    (by intro i hi; have := fr.fit i hi; omega) (by intro i hi; exact fr.ordered i (by omega))
    (by intro i hi; rw [oldT _ (upper i hi) (by have := low i hi; omega)]; exact fr.empty i hi)
    (by intro j' hji i lo hi; rw [oldT _ (lt_of_lt_of_le hi (upper (j'+1) (by omega)) |>.le) (by have := low j' (by omega); omega)]; exact fr.filled j' (by omega) i lo hi)
    (by intro i hi; have := safe (4+2*i) (by omega); omega)
    (by intro i hi v; exact rows.outEnter i (by omega) v)
    (by intro i hi v; exact rows.outScan i (by omega) v)
    (by intro i hi; exact rows.outEnd i (by omega))
  rw [show s+3+2*(j+1)=s+5+2*j by omega] at out
  have f := step_keep (k := k) (P := P) (s+5+2*j) (s+6+2*j) Z (Z+1) T .right
    (by have hv := safe (5+2*j) (by omega); omega) (by have hv := safe (5+2*j) (by omega); omega) (by omega) (by omega) (rows.write _) rfl
  have g := sweepR (Cursor.q k (s+6+2*j)) T (Z+1) c
    (by simp only [Cursor.q,small_mod k (s+6+2*j) (by have := safe (6+2*j) (by omega); omega)]; exact (by have hv := safe (6+2*j) (by omega); omega))
    (P := P) (by omega) (by intro i lo hi; simp only [T,put,show i ≠ h by omega,↓reduceIte,B,fill]; rw [if_pos (by omega)]; exact rows.appendScan false)
  rw [show Z+1+c=Z+c+1 by omega] at g
  have h0 := step_keep (k := k) (P := P) (s+6+2*j) (s+7+2*j) (Z+c+1) (Z+c+1) T .stay
    (by have hv := safe (6+2*j) (by omega); omega) (by have hv := safe (6+2*j) (by omega); omega) (by omega) (by omega)
    (by rw [show T (Z+c+1)=none by simp only [T,put,show Z+c+1 ≠ h by omega,↓reduceIte,B,fill]; rw [if_neg (by omega)]; (apply fr.fresh <;> omega)]; exact rows.appendEnd) rfl
  have h1 := step_put (k := k) (P := P) (s+7+2*j) (s+8+2*j) (Z+c+1) (Z+c) T (some false) .left
    (by have hv := safe (7+2*j) (by omega); omega) (by have hv := safe (7+2*j) (by omega); omega) (by omega) (by omega)
    (by rw [show T (Z+c+1)=none by simp only [T,put,show Z+c+1 ≠ h by omega,↓reduceIte,B,fill]; rw [if_neg (by omega)]; (apply fr.fresh <;> omega)]; exact rows.put) (by simp [dest])
  rw [add] at h1
  have backscan := sweepL (Cursor.q k (s+8+2*j)) V Z c
    (by simp only [Cursor.q,small_mod k (s+8+2*j) (by have := safe (8+2*j) (by omega); omega)]; exact (by have hv := safe (8+2*j) (by omega); omega))
    (P := P) (by omega) (by intro i lo hi; simp only [V,put,show i ≠ h by omega,↓reduceIte,E,fill]; rw [if_pos (by omega)]; exact rows.ret false)
  have backEnd := step_keep (k := k) (P := P) (s+8+2*j) (s+9+2*j) Z Z V .stay
    (by have hv := safe (8+2*j) (by omega); omega) (by have hv := safe (8+2*j) (by omega); omega) (by omega) (by omega)
    (by rw [oldV _ le_rfl (by omega),fr.empty (j+1) le_rfl]; exact rows.retEnd) rfl
  let Rev := fun i => D (j+1-i)
  obtain ⟨ti,hti,inpath⟩ := crossL k P (s+9+2*j) (j+1) Rev V
    (by intro i hi; change D (j+1-i) ≤ P; have := fr.fit (j+1-i) (by omega); omega)
    (by intro i hi
        change D (j+1-(i+1)) < D (j+1-i)
        rw [show j+1-(i+1)=j-i by omega,show j+1-i=(j-i)+1 by omega]
        exact fr.ordered (j-i) (by omega))
    (by intro i hi
        change V (D (j+1-i))=none
        rw [oldV _ (upper _ (by omega)) (by have := low (j+1-i) (by omega); omega)]
        exact fr.empty _ (by omega))
    (by intro j' hji i lo hi
        change D (j+1-(j'+1)) < i at lo
        change i < D (j+1-j') at hi
        rw [show j+1-(j'+1)=j-j' by omega] at lo
        rw [show j+1-j'=(j-j')+1 by omega] at hi
        rw [oldV _ (hi.le.trans (upper _ (by omega))) (by have := low (j-j') (by omega); omega)]
        exact fr.filled _ (by omega) i lo hi)
    (by intro i hi; have := safe (10+2*j+2*i) (by omega); omega)
    (by intro i hi v; exact rows.inEnter i (by omega) v)
    (by intro i hi v; exact rows.inScan i (by omega) v)
    (by intro i hi; exact rows.inEnd i (by omega))
  have rev0 : Rev 0=Z := rfl
  have revEnd : Rev (j+1)=D 0 := by simp [Rev]
  rw [rev0,revEnd,show s+9+2*j+2*(j+1)=s+11+4*j by omega] at inpath
  have seek0 := step_keep (k := k) (P := P) (s+11+4*j) (s+12+4*j) (D 0) (D 0-1) V .left
    (by have hv := safe (11+4*j) (by omega); omega) (by have hv := safe (11+4*j) (by omega); omega) (by omega) (by omega) (rows.hole _) rfl
  have seek := sweepL (Cursor.q k (s+12+4*j)) V h (r-c-1)
    (by simp only [Cursor.q,small_mod k (s+12+4*j) (by have := safe (12+4*j) (by omega); omega)]; exact (by have hv := safe (12+4*j) (by omega); omega))
    (P := P) (by omega) (by intro i lo hi; rw [oldV _ (by omega) (by omega),fr.bits _ (by omega) (by omega)]; exact rows.seek true)
  rw [show h+(r-c-1)=D 0-1 by omega] at seek
  have done0 := step_put (k := k) (P := P) (s+12+4*j) (s+1) h (h+1) V (some true) .right
    (by have hv := safe (12+4*j) (by omega); omega) (by have hv := safe (12+4*j) (by omega); omega) (by omega) (by omega)
    (by simp only [V,put,↓reduceIte]; exact rows.restore) rfl
  rw [restore] at done0
  have path := a.append b |>.append e |>.append out |>.append f |>.append g |>.append h0 |>.append h1 |>.append backscan |>.append backEnd |>.append inpath |>.append seek0 |>.append seek |>.append done0
  dsimp only [s,h,Z,B,T,V,E] at path
  rw [show d+c+1+1=d+c+2 by omega] at path
  refine ⟨_,?_,path⟩
  have rfit : r ≤ P := by have := fr.fit 0 (by omega); omega
  have outlim : outTime ≤ 4*(P+2) := hto.trans (Nat.mul_le_mul_right (P+2) (by omega))
  have inlim : ti ≤ 4*(P+2) := hti.trans (Nat.mul_le_mul_right (P+2) (by omega))
  omega
private theorem clone_iteration (k P d r j : Nat) (D : Nat → Nat) (C : Nat → Option Bool)
    (hj : j ≤ 3) (fr : CopyFrame C P d r j D) (a c : Nat) (ha : c+a=r) :
    ∃ t, t ≤ a*16*(P+2) ∧ Path k P t
      ⟨Cursor.q k (copyBase j+1),d+c+1,fill C (D (j+1)) c⟩
      ⟨Cursor.q k (copyBase j+1),d+r+1,fill C (D (j+1)) r⟩ := by
  induction a generalizing c with
  | zero =>
    have same : c=r := by omega
    subst c
    refine ⟨0,by omega,Path.nil _ ?_⟩
    change d+r+1 ≤ P
    have := fr.fit 0 (by omega)
    rw [fr.anchor] at this
    omega
  | succ a ih =>
    obtain ⟨u,hu,one⟩ := clone_round k P d r j c D C hj (by omega) fr
    obtain ⟨t,ht,rest⟩ := ih (c+1) (by omega)
    have connect : d+c+2=d+(c+1)+1 := by omega
    rw [connect] at one
    refine ⟨_,?_,one.append rest⟩
    nlinarith
private theorem clone_stage (k P d r j : Nat) (D : Nat → Nat) (C : Nat → Option Bool)
    (hj : j ≤ 3) (fr : CopyFrame C P d r j D) :
    ∃ t, t ≤ (16*r+2)*(P+2) ∧ Path k P t
      ⟨Cursor.q k (copyBase j),d,C⟩
      ⟨Cursor.q k (copyBase (j+1)),d,fill C (D (j+1)) r⟩ := by
  let s := copyBase j
  let E := fill C (D (j+1)) r
  have rows := copy_rows k j hj
  have fit := fr.fit 0 (by omega)
  have anc := fr.anchor
  have hi := fr.after (j+1) le_rfl
  have a := step_keep (k := k) (P := P) s (s+1) d (d+1) C .right
    (by dsimp only [s,copyBase]; omega) (copy_safe j 0 hj (by omega)).2
    (by omega) (by omega) (rows.start _) rfl
  obtain ⟨u,hu,path⟩ := clone_iteration k P d r j D C hj fr r 0 (by omega)
  rw [fill_zero] at path
  have old (i : Nat) (bound : i ≤ D 0) : E i=C i :=
    fill_old C _ _ _ (Or.inl (bound.trans (by rw [anc]; exact hi)))
  have b := step_keep (k := k) (P := P) (s+1) (s+13+4*j) (D 0) (D 0-1) E .left
    (by have hv := copy_safe j 1 hj (by omega); omega) (by have hv := copy_safe j 1 hj (by omega); omega) (by omega) (by omega)
    (by rw [old _ le_rfl,fr.empty 0 (by omega)]; exact rows.stop) rfl
  have c := sweepL (Cursor.q k (s+13+4*j)) E d r
    (by simp only [Cursor.q,small_mod k (s+13+4*j) (by have hv := copy_safe j (13+4*j) hj le_rfl; omega)]; exact (by have hv := copy_safe j (13+4*j) hj le_rfl; omega))
    (P := P) (by omega) (by intro i lo hi; rw [old _ (by omega),fr.bits i lo (by omega)]; exact rows.doneScan true)
  rw [show d+r=D 0-1 by omega] at c
  have e := step_keep (k := k) (P := P) (s+13+4*j) (s+14+4*j) d d E .stay
    (by have hv := copy_safe j (13+4*j) hj le_rfl; omega) (by have hv := copy_safe j (13+4*j) hj le_rfl; omega) (by omega) (by omega)
    (by rw [old _ (by omega),fr.left]; exact rows.doneEnd) rfl
  rw [← anc] at path
  have whole := a.append path |>.append b |>.append c |>.append e
  have next : s+14+4*j=copyBase (j+1) := by dsimp only [s,copyBase]; ring
  rw [next] at whole
  refine ⟨_,?_,whole⟩
  have rfit : r ≤ P := by omega
  nlinarith
private def bankD (F r n i : Nat) : Nat := if i=0 then F+r+2 else F+i*r+n+i+2
private def banks (C : Nat → Option Bool) (F r n : Nat) : Nat → (Nat → Option Bool)
  | 0 => C
  | j+1 => fill (banks C F r n j) (bankD F r n (j+1)) r
private theorem banks_eval (C : Nat → Option Bool) (F r n j i : Nat) :
    banks C F r n j i=(if ∃ h : Fin j, bankD F r n (h.val+1) < i ∧ i ≤ bankD F r n (h.val+1)+r then some false else C i) := by
  induction j with
  | zero => simp [banks]
  | succ j ih =>
    have split : (∃ h : Fin (j+1), bankD F r n (h.val+1) < i ∧ i ≤ bankD F r n (h.val+1)+r) ↔
        (∃ h : Fin j, bankD F r n (h.val+1) < i ∧ i ≤ bankD F r n (h.val+1)+r) ∨
          (bankD F r n (j+1) < i ∧ i ≤ bankD F r n (j+1)+r) := by
      constructor
      · rintro ⟨h,hh⟩
        by_cases lt : h.val < j
        · exact Or.inl ⟨⟨h.val,lt⟩,hh⟩
        · have eq : h.val=j := by omega
          exact Or.inr (by simpa only [eq] using hh)
      · rintro (⟨h,hh⟩ | hh)
        · exact ⟨⟨h.val,by omega⟩,hh⟩
        · exact ⟨⟨j,by omega⟩,hh⟩
    rw [banks,fill,ih]
    simp only [split]
    by_cases h : bankD F r n (j+1) < i ∧ i ≤ bankD F r n (j+1)+r <;> simp [h]
private theorem workspace_image (C : Nat → Option Bool) (L n F r : Nat) (room : L+n+1 < F) :
    banks (nimage C L n (F+r+2) n) F r n 4=Target.image C L n F r := by
  funext i
  rw [banks_eval]
  simp [Fin.exists_fin_succ,bankD,nimage,Target.image]
  all_goals split_ifs <;> first | rfl | omega
private theorem bank_empty (C : Nat → Option Bool) (L n Q F r j : Nat)
    (fr : NFrame C L n Q F r) (hj : j ≤ 3) (i : Nat) (hi : i ≤ j+1) :
    banks (nimage C L n (F+r+2) n) F r n j (bankD F r n i)=none := by
  have room := fr.room
  interval_cases j <;> interval_cases i <;> rw [banks_eval]
  all_goals simp only [Fin.exists_fin_succ,Fin.val_zero,Fin.val_succ,IsEmpty.exists_iff,or_false,Nat.reduceAdd,Nat.succ_ne_zero,Nat.one_mul,bankD,nimage,↓reduceIte]
  all_goals split_ifs <;> first | omega | (apply fr.fresh <;> omega)
private theorem bank_filled (C : Nat → Option Bool) (L n Q F r j : Nat)
    (fr : NFrame C L n Q F r) (hj : j ≤ 3) (h : Nat) (hh : h ≤ j) (i : Nat)
    (lo : bankD F r n h < i) (hi : i < bankD F r n (h+1)) :
    ∃ b, banks (nimage C L n (F+r+2) n) F r n j i=some b := by
  have room := fr.room
  interval_cases j <;> interval_cases h <;> rw [banks_eval]
  all_goals simp only [Fin.exists_fin_succ,Fin.val_zero,Fin.val_succ,IsEmpty.exists_iff,or_false,Nat.reduceAdd,Nat.succ_ne_zero,Nat.one_mul,bankD,nimage,↓reduceIte] at *
  all_goals split_ifs <;> first | omega | exact ⟨false,rfl⟩
private theorem bank_left (C : Nat → Option Bool) (L n Q F r j : Nat)
    (fr : NFrame C L n Q F r) (hj : j ≤ 3) : banks (nimage C L n (F+r+2) n) F r n j (F+1)=none := by
  have room := fr.room
  interval_cases j <;> rw [banks_eval]
  all_goals simp only [Fin.exists_fin_succ,Fin.val_zero,Fin.val_succ,IsEmpty.exists_iff,or_false,Nat.reduceAdd,Nat.succ_ne_zero,Nat.one_mul,bankD,nimage,↓reduceIte]
  all_goals split_ifs <;> first | omega | exact fr.d0
private theorem bank_bits (C : Nat → Option Bool) (L n Q F r j : Nat)
    (fr : NFrame C L n Q F r) (hj : j ≤ 3) (i : Nat) (lo : F+1 < i) (hi : i < F+1+r+1) :
    banks (nimage C L n (F+r+2) n) F r n j i=some true := by
  have room := fr.room
  interval_cases j <;> rw [banks_eval]
  all_goals simp only [Fin.exists_fin_succ,Fin.val_zero,Fin.val_succ,IsEmpty.exists_iff,or_false,Nat.reduceAdd,Nat.succ_ne_zero,Nat.one_mul,bankD,nimage,↓reduceIte]
  all_goals split_ifs <;> first | omega | (apply fr.bank0 <;> omega)
private theorem bank_fresh (C : Nat → Option Bool) (L n Q F r j : Nat)
    (fr : NFrame C L n Q F r) (hj : j ≤ 3) (i : Nat) (lo : bankD F r n (j+1) ≤ i)
    (hi : i ≤ bankD F r n (j+1)+r+1) : banks (nimage C L n (F+r+2) n) F r n j i=none := by
  have room := fr.room
  interval_cases j <;> rw [banks_eval]
  all_goals simp only [Fin.exists_fin_succ,Fin.val_zero,Fin.val_succ,IsEmpty.exists_iff,or_false,Nat.reduceAdd,Nat.succ_ne_zero,Nat.one_mul,bankD,nimage,↓reduceIte] at *
  all_goals split_ifs <;> first | omega | (apply fr.fresh <;> omega)
private theorem bank_frame (C : Nat → Option Bool) (L n Q F r j : Nat)
    (fr : NFrame C L n Q F r) (hj : j ≤ 3) :
    CopyFrame (banks (nimage C L n (F+r+2) n) F r n j) (F+5*r+n+7) (F+1) r j (bankD F r n) := by
  have room := fr.room
  constructor
  · simp [bankD]; omega
  · intro i hi
    by_cases iz : i=0
    · subst i; simp only [bankD,↓reduceIte]; omega
    · have mul := Nat.mul_le_mul_right r (show i ≤ 4 by omega)
      simp only [bankD,iz,↓reduceIte]; omega
  · intro i hi
    by_cases iz : i=0
    · subst i; simp only [bankD,↓reduceIte]; omega
    · have mul := Nat.mul_le_mul_right r (show 1 ≤ i by omega)
      simp only [bankD,iz,↓reduceIte]; omega
  · intro i hi
    by_cases iz : i=0
    · subst i; simp [bankD]; omega
    · simp only [bankD,iz,show i+1 ≠ 0 by omega,↓reduceIte,Nat.add_mul,Nat.one_mul]
      omega
  · exact bank_empty C L n Q F r j fr hj
  · exact bank_filled C L n Q F r j fr hj
  · exact bank_left C L n Q F r j fr hj
  · exact bank_bits C L n Q F r j fr hj
  · exact bank_fresh C L n Q F r j fr hj
private theorem setup_entry (k S L n F r : Nat) (C : Nat → Option Bool)
    (sl : S < L) (room : L+n+1 < F) (eof : C S=none)
    (reg : ∀ i, S < i → i < L → C i=some false) (sep : C L=none)
    (assn : ∀ i, L < i → i < L+n+1 → C i=some false) (right : C (L+n+1)=none) :
    Path k (F+5*r+n+7) (L-S+n+2) ⟨Cursor.rReady k,S,C⟩ ⟨Cursor.q k 101,L+n+1,C⟩ := by
  let P := F+5*r+n+7
  have a := step_keep (k := k) (P := P) 98 99 S (S+1) C .right
    (by omega) (by omega) (by omega) (by omega)
    (by rw [eof]; exact row_value k 98 none (by omega) (by omega)) rfl
  have b := sweepR (Cursor.q k 99) C (S+1) (L-S-1)
    (by simp only [Cursor.q,small_mod k 99 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [reg i (by omega) (by omega)]; exact row_value k 99 (some false) (by omega) (by omega))
  rw [show S+1+(L-S-1)=L by omega] at b
  have c := step_keep (k := k) (P := P) 99 100 L (L+1) C .right
    (by omega) (by omega) (by omega) (by omega)
    (by rw [sep]; exact row_value k 99 none (by omega) (by omega)) rfl
  have d := sweepR (Cursor.q k 100) C (L+1) n
    (by simp only [Cursor.q,small_mod k 100 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [assn i (by omega) (by omega)]; exact row_value k 100 (some false) (by omega) (by omega))
  rw [show L+1+n=L+n+1 by omega] at d
  have e := step_keep (k := k) (P := P) 100 101 (L+n+1) (L+n+1) C .stay
    (by omega) (by omega) (by omega) (by omega)
    (by rw [right]; exact row_value k 100 none (by omega) (by omega)) rfl
  have path := a.append b |>.append c |>.append d |>.append e
  convert path using 1
  omega
private theorem Path.first {k N B P t c d} (path : Path k P t c d) (hp : P < tapeLength N B)
    (u : Nat) (hu : u < t) :
    ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val < 201 := by
  induction path generalizing u with
  | nil => omega
  | @cons t c d e edge rest ih =>
    cases u with
    | zero => exact edge.safe
    | succ u =>
      have one : Path k P 1 c d := Path.cons edge (Path.nil d edge.after)
      rw [show u+1=1+u by omega,UniformTM.run_add,one.execute hp]
      exact ih u (by omega)
/-- Same Cursor table: counted suffix to first complete workspace, before destructive halving. -/
theorem workspace (k N B S L n Q F r : Nat) (C : Nat → Option Bool)
    (sl : S < L) (paid : 0 < Q) (room : L+n+1+Q < F)
    (eof : C S=none) (reg : ∀ i, S < i → i < L → C i=some false)
    (sep : C L=none) (assn : ∀ i, L < i → i < L+n+1 → C i=some false)
    (right : C (L+n+1)=none)
    (marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → C i=some true)
    (gap : ∀ i, L+n+1+Q < i → i < F → C i=none)
    (fence : C F=some false) (d0 : C (F+1)=none)
    (bank0 : ∀ i, F+1 < i → i < F+r+2 → C i=some true)
    (fresh : ∀ i, F+r+2 ≤ i → i ≤ F+5*r+n+7 → C i=none)
    (fit : F+5*r+n+7 < tapeLength N B) :
    ∃ t, t ≤ 128*(n+r+1)*(F+5*r+n+9) ∧
      (Cursor.machine k).run t (⟨Cursor.rReady k,⟨S,by omega⟩,fun i => C i.val⟩ : Config (Cursor.machine k).stateCount N B)=
        ⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => Target.image C L n F r i.val⟩ ∧
      (∀ u, u < t → ((Cursor.machine k).run u
        (⟨Cursor.rReady k,⟨S,by omega⟩,fun i => C i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 201) := by
  have fr : NFrame C L n Q F r := ⟨paid,room,sep,assn,right,marks,gap,fence,d0,bank0,fresh⟩
  have pre := setup_entry k S L n F r C sl (by omega) eof reg sep assn right
  obtain ⟨v,hv,install⟩ := n_iteration k C L n Q F r n 0 fr (by omega)
  rw [n_zero] at install
  have finish := n_finish k C L n Q F r fr
  let C0 := nimage C L n (F+r+2) n
  obtain ⟨t0,h0,p0⟩ := clone_stage k (F+5*r+n+7) (F+1) r 0 (bankD F r n) C0 (by omega) (bank_frame C L n Q F r 0 fr (by omega))
  obtain ⟨t1,h1,p1⟩ := clone_stage k (F+5*r+n+7) (F+1) r 1 (bankD F r n) (banks C0 F r n 1) (by omega) (bank_frame C L n Q F r 1 fr (by omega))
  obtain ⟨t2,h2,p2⟩ := clone_stage k (F+5*r+n+7) (F+1) r 2 (bankD F r n) (banks C0 F r n 2) (by omega) (bank_frame C L n Q F r 2 fr (by omega))
  obtain ⟨t3,h3,p3⟩ := clone_stage k (F+5*r+n+7) (F+1) r 3 (bankD F r n) (banks C0 F r n 3) (by omega) (bank_frame C L n Q F r 3 fr (by omega))
  have path := pre.append install |>.append finish |>.append p0 |>.append p1 |>.append p2 |>.append p3
  have image : banks C0 F r n 4=Target.image C L n F r := workspace_image C L n F r (by omega)
  change Path k _ _ _ ⟨Cursor.q k 201,F+1,banks C0 F r n 4⟩ at path
  rw [image] at path
  refine ⟨_,?_,path.execute fit,path.first fit⟩
  have height : n ≤ F+5*r+n+7 := by omega
  have init : L-S+n+2 ≤ 2*(F+5*r+n+9) := by omega
  have tail : 2*n+(F-(L+n+1))+5 ≤ 3*(F+5*r+n+9) := by omega
  have basePrice : 2*(F-(L+n+1))+2*r+4*n+13 ≤ 8*(F+5*r+n+9) := by omega
  have price : v ≤ 8*n*(F+5*r+n+9) := by
    have h := hv.trans (Nat.mul_le_mul_left n basePrice)
    nlinarith
  nlinarith
end CappedWorkspace
