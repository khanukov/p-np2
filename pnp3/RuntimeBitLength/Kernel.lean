import RuntimeBitLength.Rows
namespace RuntimeBitLength
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
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
  safe : c.state.val < 254
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
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hs : s.val < 254) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hs,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
/-- One exact public row that preserves the scanned symbol. -/
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hs : s.val < 254) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hs hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (hs : s.val < 254) (fit : h+r   ≤   P) (rows : ∀ i, h   ≤   i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right hs (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (hs : s.val < 254) (fit : low+r   ≤   P) (rows : ∀ i, low < i → i   ≤   low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left hs (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private theorem Path.first {k N B P t c d} (path : Path k P t c d) (hp : P < tapeLength N B)
    (u : Nat) (hu : u < t) :
    ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val < 254 := by
  induction path generalizing u with
  | nil => omega
  | @cons t c d e edge rest ih =>
    cases u with
    | zero => exact edge.safe
    | succ u =>
      have one : Path k P 1 c d := Path.cons edge (Path.nil d edge.after)
      rw [show u+1=1+u by omega,UniformTM.run_add,one.execute hp]
      exact ih u (by omega)
private theorem small_mod (k i : Nat) (h : i ≤ 329) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)

private theorem row_value (k i : Nat) (b : Option Bool) (lo : 201 ≤ i) (hi : i < 250) :
    let code := instructions[3*(i-201)+(match b with | none => 0 | some false => 1 | some true => 2)]!
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply phase_row k i _ b lo hi
  have len : instructions.length=147 := rfl
  have bound : 3*(i-201)+(match b with | none => 0 | some false => 1 | some true => 2) < instructions.length := by
    rw [len]; split <;> omega
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some]
  exact List.getElem?_eq_getElem bound
private theorem step_keep {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (mv : Move)
    (hs : 201 ≤ s) (ht : s < 250) (hb : h ≤ P) (ha : h' ≤ P)
    (row : (Cursor.machine k).step (Cursor.q k s) (T h)=(Cursor.q k d,T h,mv))
    (hm : dest h mv=h') : Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ :=
  keep _ _ _ _ _ _ (by simp only [Cursor.q,small_mod k s (by omega)]; omega) hb ha row hm
private theorem step_put {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (out : Option Bool) (mv : Move)
    (hs : 201 ≤ s) (ht : s < 250) (hb : h ≤ P) (ha : h' ≤ P)
    (row : (Cursor.machine k).step (Cursor.q k s) (T h)=(Cursor.q k d,out,mv))
    (hm : dest h mv=h') : Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',put T h out⟩ :=
  hop _ _ _ _ _ _ _ (by simp only [Cursor.q,small_mod k s (by omega)]; omega) hb ha row hm
private structure Frame (X : Nat → Option Bool) (L n Q F r : Nat) : Prop where
  positive : 0 < Q
  room : L+n+1+Q < F
  sep : X L=none
  assn : ∀ i, L < i → i < L+n+1 → X i=some true
  right : X (L+n+1)=none
  marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → X i=some true
  gap : ∀ i, L+n+1+Q < i → i < F → X i=none
  fence : X F=some false
  d0 : X (F+1)=none
  b0 : ∀ i, F+1 < i → i < F+r+2 → X i=some true
  d1 : X (F+r+2)=none
  b1 : ∀ i, F+r+2 < i → i < F+r+n+3 → X i=some false
  d2 : X (F+r+n+3)=none
  b2 : X (F+r+n+4)=some false
private def data (X : Nat → Option Bool) (L D u v : Nat) : Nat → Option Bool := fun i =>
  if L < i ∧ i ≤ L+u then some false else
  if D < i ∧ i ≤ D+v then some true else X i
private theorem data_zero (X : Nat → Option Bool) (L D : Nat) : data X L D 0 0=X := by
  funext i; simp only [data]; rw [if_neg (by omega),if_neg (by omega)]
private theorem outside (X : Nat → Option Bool) (L D u v i : Nat)
    (ha : i ≤ L ∨ L+u < i) (hb : i ≤ D ∨ D+v < i) : data X L D u v i=X i := by
  simp only [data]; rw [if_neg (by omega),if_neg (by omega)]
private theorem digit {X L n Q F r} (fr : Frame X L n Q F r) (u v i : Nat)
    (lo : L < i) (hi : i < L+n+1) :
    data X L (F+r+2) u v i=some (decide (L+u < i)) := by
  have room := fr.room
  simp only [data]; rw [if_neg (show ¬(F+r+2 < i ∧ i ≤ F+r+2+v) by omega)]
  by_cases h : i ≤ L+u
  · rw [if_pos ⟨lo,h⟩]; simp only [show ¬L+u < i by omega,decide_false]
  · rw [if_neg (by omega),fr.assn i lo hi]; simp only [show L+u < i by omega,decide_true]
private theorem bank {X L n Q F r} (fr : Frame X L n Q F r) (u v i : Nat)
    (hu : u ≤ n) (lo : F+r+2 < i) (hi : i < F+r+n+3) :
    data X L (F+r+2) u v i=some (decide (i ≤ F+r+2+v)) := by
  have room := fr.room
  simp only [data]; rw [if_neg (by omega)]
  by_cases h : i ≤ F+r+2+v
  · rw [if_pos ⟨lo,h⟩]; simp only [h,decide_true]
  · rw [if_neg (by omega),fr.b1 i lo hi]; simp only [h,decide_false]
private theorem advance (X : Nat → Option Bool) (L D u v : Nat) (room : L+u+1 < D) :
    put (data X L D u v) (L+u+1) (some false)=data X L D (u+1) v := by
  funext i; simp only [put,data]; split_ifs <;> first | rfl | omega
private theorem append_bit (X : Nat → Option Bool) (L D u v : Nat) (room : L+u < D) :
    put (data X L D u v) (D+v+1) (some true)=data X L D u (v+1) := by
  funext i; simp only [put,data]; split_ifs <;> first | rfl | omega
/-- A proof helper: one literal row, preserving its actual occupied/blank symbol. -/
private theorem K {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (mv : Move)
    (lo : 201 ≤ s) (hi : s < 250) (hb : h ≤ P) (ha : h' ≤ P) (value : T h=b)
    (row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k d,b,mv)) (hm : dest h mv=h') :
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ :=
  step_keep s d h h' T mv lo hi hb ha (by rw [value]; exact row) hm
private theorem entry (k L n Q F r : Nat) (X : Nat → Option Bool) (fr : Frame X L n Q F r) :
    ∃ t, t=F-L+5 ∧ t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k 201,F+1,X⟩ ⟨Cursor.q k 209,L,X⟩ := by
  let P := F+5*r+n+7
  let H := L+n+1
  have room := fr.room
  have paid := fr.positive
  have a := K (k := k) (P := P) 201 202 (F+1) (F+1) X none .stay
    (by omega) (by omega) (by omega) (by omega) fr.d0 (row_value k 201 none (by omega) (by omega)) rfl
  have b := K (k := k) (P := P) 202 203 (F+1) F X none .left
    (by omega) (by omega) (by omega) (by omega) fr.d0 (row_value k 202 none (by omega) (by omega)) (by simp [dest])
  have c := K (k := k) (P := P) 203 204 F (F-1) X (some false) .left
    (by omega) (by omega) (by omega) (by omega) fr.fence (row_value k 203 (some false) (by omega) (by omega)) rfl
  have d := sweepL (Cursor.q k 204) X (H+Q) (F-(H+Q)-1)
    (by simp only [Cursor.q,small_mod k 204 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.gap i (by omega) (by omega)]; exact row_value k 204 none (by omega) (by omega))
  rw [show H+Q+(F-(H+Q)-1)=F-1 by omega] at d
  have e := K (k := k) (P := P) 204 205 (H+Q) (H+(Q-1)) X (some true) .left
    (by omega) (by omega) (by omega) (by omega) (fr.marks _ (by omega) (by omega))
    (row_value k 204 (some true) (by omega) (by omega)) (by change H+Q-1=H+(Q-1); omega)
  have f := sweepL (Cursor.q k 205) X H (Q-1)
    (by simp only [Cursor.q,small_mod k 205 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.marks i (by omega) (by omega)]; exact row_value k 205 (some true) (by omega) (by omega))
  have g := K (k := k) (P := P) 205 206 H H X none .stay
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 205 none (by omega) (by omega)) rfl
  have h := K (k := k) (P := P) 206 207 H (L+n) X none .left
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 206 none (by omega) (by omega)) (by simp [dest,H])
  have i := sweepL (Cursor.q k 207) X L n
    (by simp only [Cursor.q,small_mod k 207 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.assn i lo (by omega)]; exact row_value k 207 (some true) (by omega) (by omega))
  have j := K (k := k) (P := P) 207 208 L L X none .stay
    (by omega) (by omega) (by omega) (by omega) fr.sep (row_value k 207 none (by omega) (by omega)) rfl
  have l := K (k := k) (P := P) 208 209 L L X none .stay
    (by omega) (by omega) (by omega) (by omega) fr.sep (row_value k 208 none (by omega) (by omega)) rfl
  exact ⟨_,by dsimp [H]; omega,by dsimp [P,H]; omega,a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h |>.append i |>.append j |>.append l⟩
private structure Travel (T : Nat → Option Bool) (L n Q F r : Nat) : Prop where
  positive : 0 < Q
  room : L+n+1+Q < F
  sep : T L=none
  assn : ∀ i, L < i → i < L+n+1 → ∃ b, T i=some b
  right : T (L+n+1)=none
  marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → T i=some true
  gap : ∀ i, L+n+1+Q < i → i < F → T i=none
  fence : T F=some false
  d0 : T (F+1)=none
  b0 : ∀ i, F+1 < i → i < F+r+2 → T i=some true
  d1 : T (F+r+2)=none
  b1 : ∀ i, F+r+2 < i → i < F+r+n+3 → ∃ b, T i=some b
  d2 : T (F+r+n+3)=none
  b2 : T (F+r+n+4)=some false
private theorem travel {X L n Q F r} (fr : Frame X L n Q F r) (u v : Nat) (hu : u ≤ n) (hv : v ≤ n) :
    Travel (data X L (F+r+2) u v) L n Q F r := by
  have room := fr.room
  have old (i) (ha : i ≤ L ∨ L+n < i) (hb : i ≤ F+r+2 ∨ F+r+2+n < i) :
      data X L (F+r+2) u v i=X i := outside X L (F+r+2) u v i (by omega) (by omega)
  refine ⟨fr.positive,room,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [old _ (by omega) (by omega)]; exact fr.sep
  · intro i lo hi; exact ⟨_,digit fr u v i lo hi⟩
  · rw [old _ (by omega) (by omega)]; exact fr.right
  · intro i lo hi; rw [old _ (by omega) (by omega)]; exact fr.marks i lo hi
  · intro i lo hi; rw [old _ (by omega) (by omega)]; exact fr.gap i lo hi
  · rw [old _ (by omega) (by omega)]; exact fr.fence
  · rw [old _ (by omega) (by omega)]; exact fr.d0
  · intro i lo hi; rw [old _ (by omega) (by omega)]; exact fr.b0 i lo hi
  · rw [old _ (by omega) (by omega)]; exact fr.d1
  · intro i lo hi; exact ⟨_,bank fr u v i hu lo hi⟩
  · rw [old _ (by omega) (by omega)]; exact fr.d2
  · rw [old _ (by omega) (by omega)]; exact fr.b2
private theorem outward (k L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r) :
    ∃ t, t=F-L+r+4 ∧ t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k 217,L,T⟩ ⟨Cursor.q k 223,F+r+2,T⟩ := by
  let P := F+5*r+n+7
  let H := L+n+1
  have room := fr.room
  have a := K (k := k) (P := P) 217 218 L (L+1) T none .right
    (by omega) (by omega) (by omega) (by omega) fr.sep (row_value k 217 none (by omega) (by omega)) rfl
  have b := sweepR (Cursor.q k 218) T (L+1) n
    (by simp only [Cursor.q,small_mod k 218 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; obtain ⟨b,hb⟩ := fr.assn i (by omega) (by omega); rw [hb]; cases b <;> exact row_value k 218 _ (by omega) (by omega))
  rw [show L+1+n=H by omega] at b
  have c := K (k := k) (P := P) 218 219 H H T none .stay
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 218 none (by omega) (by omega)) rfl
  have d := K (k := k) (P := P) 219 220 H (H+1) T none .right
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 219 none (by omega) (by omega)) rfl
  have e := sweepR (Cursor.q k 220) T (H+1) (F-H-1)
    (by simp only [Cursor.q,small_mod k 220 (by omega)]; omega) (P := P) (by omega)
    (by
      intro i lo hi
      by_cases hiQ : i ≤ H+Q
      · rw [fr.marks i (by omega) (by omega)]; exact row_value k 220 (some true) (by omega) (by omega)
      · rw [fr.gap i (by omega) (by omega)]; exact row_value k 220 none (by omega) (by omega))
  rw [show H+1+(F-H-1)=F by omega] at e
  have f := K (k := k) (P := P) 220 221 F (F+1) T (some false) .right
    (by omega) (by omega) (by omega) (by omega) fr.fence (row_value k 220 (some false) (by omega) (by omega)) rfl
  have g := K (k := k) (P := P) 221 222 (F+1) (F+2) T none .right
    (by omega) (by omega) (by omega) (by omega) fr.d0 (row_value k 221 none (by omega) (by omega)) rfl
  have h := sweepR (Cursor.q k 222) T (F+2) r
    (by simp only [Cursor.q,small_mod k 222 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.b0 i (by omega) (by omega)]; exact row_value k 222 (some true) (by omega) (by omega))
  rw [show F+2+r=F+r+2 by omega] at h
  have j := K (k := k) (P := P) 222 223 (F+r+2) (F+r+2) T none .stay
    (by omega) (by omega) (by omega) (by omega) fr.d1 (row_value k 222 none (by omega) (by omega)) rfl
  exact ⟨_,by dsimp [H]; omega,by dsimp [P,H]; omega,a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h |>.append j⟩
private theorem inward (k L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r) :
    ∃ t, t=F-L+r+5 ∧ t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k 227,F+r+2,T⟩ ⟨Cursor.q k 213,L,T⟩ := by
  let P := F+5*r+n+7
  let H := L+n+1
  have room := fr.room
  have paid := fr.positive
  have a := K (k := k) (P := P) 227 228 (F+r+2) (F+r+1) T none .left
    (by omega) (by omega) (by omega) (by omega) fr.d1 (row_value k 227 none (by omega) (by omega)) (by simp [dest])
  have b := sweepL (Cursor.q k 228) T (F+1) r
    (by simp only [Cursor.q,small_mod k 228 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.b0 i lo (by omega)]; exact row_value k 228 (some true) (by omega) (by omega))
  rw [show F+1+r=F+r+1 by omega] at b
  have c := K (k := k) (P := P) 228 229 (F+1) (F+1) T none .stay
    (by omega) (by omega) (by omega) (by omega) fr.d0 (row_value k 228 none (by omega) (by omega)) rfl
  have d := K (k := k) (P := P) 229 230 (F+1) F T none .left
    (by omega) (by omega) (by omega) (by omega) fr.d0 (row_value k 229 none (by omega) (by omega)) (by simp [dest])
  have e := K (k := k) (P := P) 230 231 F (F-1) T (some false) .left
    (by omega) (by omega) (by omega) (by omega) fr.fence (row_value k 230 (some false) (by omega) (by omega)) rfl
  have f := sweepL (Cursor.q k 231) T (H+Q) (F-(H+Q)-1)
    (by simp only [Cursor.q,small_mod k 231 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.gap i (by omega) (by omega)]; exact row_value k 231 none (by omega) (by omega))
  rw [show H+Q+(F-(H+Q)-1)=F-1 by omega] at f
  have g := K (k := k) (P := P) 231 232 (H+Q) (H+(Q-1)) T (some true) .left
    (by omega) (by omega) (by omega) (by omega) (fr.marks _ (by omega) (by omega))
    (row_value k 231 (some true) (by omega) (by omega)) (by change H+Q-1=H+(Q-1); omega)
  have h := sweepL (Cursor.q k 232) T H (Q-1)
    (by simp only [Cursor.q,small_mod k 232 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.marks i (by omega) (by omega)]; exact row_value k 232 (some true) (by omega) (by omega))
  have j := K (k := k) (P := P) 232 233 H H T none .stay
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 232 none (by omega) (by omega)) rfl
  have l := K (k := k) (P := P) 233 234 H (L+n) T none .left
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 233 none (by omega) (by omega)) (by simp [dest,H])
  have o := sweepL (Cursor.q k 234) T L n
    (by simp only [Cursor.q,small_mod k 234 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; obtain ⟨b,hb⟩ := fr.assn i lo (by omega); rw [hb]; cases b <;> exact row_value k 234 _ (by omega) (by omega))
  have p := K (k := k) (P := P) 234 213 L L T none .stay
    (by omega) (by omega) (by omega) (by omega) fr.sep (row_value k 234 none (by omega) (by omega)) rfl
  exact ⟨_,by dsimp [H]; omega,by dsimp [P,H]; omega,a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h |>.append j |>.append l |>.append o |>.append p⟩
private theorem round (k L n Q F r c : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hc : c < n/2) (first : Bool) :
    ∃ t, t=2*(F-L)+2*r+6*c+17 ∧ t ≤ 64*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (if first then 209 else 213),L,data X L (F+r+2) (2*c) c⟩
      ⟨Cursor.q k 213,L,data X L (F+r+2) (2*(c+1)) (c+1)⟩ := by
  let P := F+5*r+n+7
  let D := F+r+2
  let seek := if first then 210 else 214
  let T := data X L D (2*c) c
  let V := data X L D (2*c+1) c
  let W := data X L D (2*c+2) c
  let E := data X L D (2*c+2) (c+1)
  have room := fr.room
  have hn : 2*c+2 ≤ n := by omega
  have tSep : T L=none := by change data X L D (2*c) c L=none; rw [outside X L D (2*c) c L (by omega) (by dsimp [D]; omega)]; exact fr.sep
  have a := K (k := k) (P := P) (if first then 209 else 213) seek L (L+1) T none .right
    (by cases first <;> decide) (by cases first <;> decide) (by omega) (by omega) tSep
    (by cases first with
      | false => exact row_value k 213 none (by decide) (by decide)
      | true => exact row_value k 209 none (by decide) (by decide)) rfl
  have b := sweepR (Cursor.q k seek) T (L+1) (2*c)
    (by change seek % Cursor.stateCount k < 254; rw [small_mod k seek (by dsimp [seek]; split <;> omega)]; dsimp [seek]; split <;> omega) (P := P) (by omega)
    (by
      intro i lo hi
      have val : T i=some false := by dsimp only [T,D]; rw [digit fr (2*c) c i (by omega) (by omega)]; simp only [show ¬L+2*c < i by omega,decide_false]
      rw [val]; cases first with
      | false => exact row_value k 214 (some false) (by decide) (by decide)
      | true => exact row_value k 210 (some false) (by decide) (by decide))
  rw [show L+1+2*c=L+2*c+1 by omega] at b
  have val1 : T (L+2*c+1)=some true := by
    dsimp only [T,D]; rw [digit fr (2*c) c (L+2*c+1) (by omega) (by omega)]; simp only [show L+2*c < L+2*c+1 by omega,decide_true]
  have d := step_put (k := k) (P := P) seek 215 (L+2*c+1) (L+2*c+2) T (some false) .right
    (by cases first <;> decide) (by cases first <;> decide) (by omega) (by omega)
    (by rw [val1]; cases first with
      | false => exact row_value k 214 (some true) (by decide) (by decide)
      | true => exact row_value k 210 (some true) (by decide) (by decide)) rfl
  rw [advance X L D (2*c) c (by dsimp [D]; omega)] at d
  have val2 : V (L+2*c+2)=some true := by
    dsimp only [V,D]; rw [digit fr (2*c+1) c (L+2*c+2) (by omega) (by omega)]; simp only [show L+(2*c+1) < L+2*c+2 by omega,decide_true]
  have e := step_put (k := k) (P := P) 215 216 (L+2*c+2) (L+2*c+1) V (some false) .left
    (by omega) (by omega) (by omega) (by omega) (by rw [val2]; exact row_value k 215 (some true) (by omega) (by omega))
    (by change L+2*c+2-1=L+2*c+1; omega)
  rw [show L+2*c+2=L+(2*c+1)+1 by omega,advance X L D (2*c+1) c (by dsimp [D]; omega)] at e
  have f := sweepL (Cursor.q k 216) W L (2*c+1)
    (by simp only [Cursor.q,small_mod k 216 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; dsimp only [W,D]; rw [digit fr (2*c+2) c i lo (by omega)]; generalize decide (L+(2*c+2) < i)=b; cases b <;> exact row_value k 216 _ (by omega) (by omega))
  have wfr := travel fr (2*c+2) c hn (by omega)
  have g := K (k := k) (P := P) 216 217 L L W none .stay
    (by omega) (by omega) (by omega) (by omega) wfr.sep (row_value k 216 none (by omega) (by omega)) rfl
  obtain ⟨ot,oe,oh,out⟩ := outward k L n Q F r W wfr
  have h := K (k := k) (P := P) 223 224 D (D+1) W none .right
    (by omega) (by omega) (by omega) (by omega) wfr.d1 (row_value k 223 none (by omega) (by omega)) rfl
  have j := sweepR (Cursor.q k 224) W (D+1) c
    (by simp only [Cursor.q,small_mod k 224 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; dsimp only [W,D]; rw [bank fr (2*c+2) c i hn (by dsimp [D] at *; omega) (by dsimp [D] at *; omega)]; simp only [show i ≤ F+r+2+c by dsimp [D] at *; omega,decide_true]; exact row_value k 224 (some true) (by omega) (by omega))
  rw [show D+1+c=D+c+1 by omega] at j
  have vj : W (D+c+1)=some false := by
    dsimp only [W,D]; rw [bank fr (2*c+2) c (D+c+1) hn (by dsimp [D]; omega) (by dsimp [D]; omega)]
    simp only [show ¬D+c+1 ≤ F+r+2+c by dsimp [D]; omega,decide_false]
  have l := step_put (k := k) (P := P) 224 225 (D+c+1) (D+c) W (some true) .left
    (by omega) (by omega) (by omega) (by omega) (by rw [vj]; exact row_value k 224 (some false) (by omega) (by omega))
    (by change D+c+1-1=D+c; omega)
  rw [append_bit X L D (2*c+2) c (by dsimp [D]; omega)] at l
  have efr := travel fr (2*c+2) (c+1) hn (by omega)
  have o := sweepL (Cursor.q k 225) E D c
    (by simp only [Cursor.q,small_mod k 225 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; obtain ⟨b,hb⟩ := efr.b1 i (by dsimp [D] at *; omega) (by dsimp [D] at *; omega); dsimp only [E,D]; rw [hb]; cases b <;> exact row_value k 225 _ (by omega) (by omega))
  have p := K (k := k) (P := P) 225 227 D D E none .stay
    (by omega) (by omega) (by omega) (by omega) efr.d1 (row_value k 225 none (by omega) (by omega)) rfl
  obtain ⟨it,ie,ih,back⟩ := inward k L n Q F r E efr
  have path := a.append b |>.append d |>.append e |>.append f |>.append g |>.append out |>.append h |>.append j |>.append l |>.append o |>.append p |>.append back
  have eq : 2*c+2=2*(c+1) := by omega
  change Path k P _ _ ⟨Cursor.q k 213,L,data X L D (2*c+2) (c+1)⟩ at path
  rw [eq] at path
  exact ⟨_,by omega,by omega,path⟩
private theorem iteration (k L n Q F r c d : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hc : c+d ≤ n/2) :
    ∃ t, t ≤ d*(64*(F+5*r+n+8)) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k 213,L,data X L (F+r+2) (2*c) c⟩
      ⟨Cursor.q k 213,L,data X L (F+r+2) (2*(c+d)) (c+d)⟩ := by
  induction d generalizing c with
  | zero =>
    have hl : L ≤ F+5*r+n+7 := by have h := fr.room; omega
    exact ⟨0,by omega,by simpa using Path.nil ⟨Cursor.q k 213,L,data X L (F+r+2) (2*c) c⟩ hl⟩
  | succ d ih =>
    obtain ⟨t,_,ht,path⟩ := round k L n Q F r c X fr (by omega) false
    obtain ⟨u,hu,rest⟩ := ih (c+1) (by omega)
    refine ⟨t+u,?_,?_⟩
    · nlinarith only [ht,hu]
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path.append rest
private theorem outward2 (k L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r) :
    ∃ t, t=F-L+r+4 ∧ t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k 236,L,T⟩ ⟨Cursor.q k 242,F+r+2,T⟩ := by
  let P := F+5*r+n+7
  let H := L+n+1
  have room := fr.room
  have a := K (k := k) (P := P) 236 237 L (L+1) T none .right
    (by omega) (by omega) (by omega) (by omega) fr.sep (row_value k 236 none (by omega) (by omega)) rfl
  have b := sweepR (Cursor.q k 237) T (L+1) n
    (by simp only [Cursor.q,small_mod k 237 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; obtain ⟨b,hb⟩ := fr.assn i (by omega) (by omega); rw [hb]; cases b <;> exact row_value k 237 _ (by omega) (by omega))
  rw [show L+1+n=H by omega] at b
  have c := K (k := k) (P := P) 237 238 H H T none .stay
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 237 none (by omega) (by omega)) rfl
  have d := K (k := k) (P := P) 238 239 H (H+1) T none .right
    (by omega) (by omega) (by omega) (by omega) fr.right (row_value k 238 none (by omega) (by omega)) rfl
  have e := sweepR (Cursor.q k 239) T (H+1) (F-H-1)
    (by simp only [Cursor.q,small_mod k 239 (by omega)]; omega) (P := P) (by omega)
    (by
      intro i lo hi
      by_cases hiQ : i ≤ H+Q
      · rw [fr.marks i (by omega) (by omega)]; exact row_value k 239 (some true) (by omega) (by omega)
      · rw [fr.gap i (by omega) (by omega)]; exact row_value k 239 none (by omega) (by omega))
  rw [show H+1+(F-H-1)=F by omega] at e
  have f := K (k := k) (P := P) 239 240 F (F+1) T (some false) .right
    (by omega) (by omega) (by omega) (by omega) fr.fence (row_value k 239 (some false) (by omega) (by omega)) rfl
  have g := K (k := k) (P := P) 240 241 (F+1) (F+2) T none .right
    (by omega) (by omega) (by omega) (by omega) fr.d0 (row_value k 240 none (by omega) (by omega)) rfl
  have h := sweepR (Cursor.q k 241) T (F+2) r
    (by simp only [Cursor.q,small_mod k 241 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [fr.b0 i (by omega) (by omega)]; exact row_value k 241 (some true) (by omega) (by omega))
  rw [show F+2+r=F+r+2 by omega] at h
  have j := K (k := k) (P := P) 241 242 (F+r+2) (F+r+2) T none .stay
    (by omega) (by omega) (by omega) (by omega) fr.d1 (row_value k 241 none (by omega) (by omega)) rfl
  exact ⟨_,by dsimp [H]; omega,by dsimp [P,H]; omega,a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h |>.append j⟩
private theorem erase_finish (k L n Q F r : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) :
    ∃ t, t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k 213,L,data X L (F+r+2) (2*(n/2)) (n/2)⟩
      ⟨Cursor.q k 236,L,data X L (F+r+2) n (n/2)⟩ := by
  let P := F+5*r+n+7
  let D := F+r+2
  let c := n/2
  let T := data X L D (2*c) c
  let E := data X L D n c
  let H := L+n+1
  have room := fr.room
  have hc : 2*c ≤ n ∧ n ≤ 2*c+1 := by dsimp [c]; omega
  have tfr := travel fr (2*c) c hc.1 (by omega)
  have efr := travel fr n c le_rfl (by omega)
  have a := K (k := k) (P := P) 213 214 L (L+1) T none .right
    (by omega) (by omega) (by omega) (by omega) tfr.sep (row_value k 213 none (by omega) (by omega)) rfl
  have b := sweepR (Cursor.q k 214) T (L+1) (2*c)
    (by simp only [Cursor.q,small_mod k 214 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; dsimp only [T,D]; rw [digit fr (2*c) c i (by omega) (by omega)]; simp only [show ¬L+2*c < i by omega,decide_false]; exact row_value k 214 (some false) (by omega) (by omega))
  rw [show L+1+2*c=L+2*c+1 by omega] at b
  have tail : ∃ t, t ≤ 2 ∧ Path k P t
      ⟨Cursor.q k 214,L+2*c+1,T⟩ ⟨Cursor.q k 235,L+n,E⟩ := by
    by_cases even : 2*c=n
    · have same : T=E := by dsimp only [T,E]; rw [even]
      rw [show L+2*c+1=H by omega,same]
      have e := K (k := k) (P := P) 214 235 H (L+n) E none .left
        (by omega) (by omega) (by omega) (by omega) efr.right (row_value k 214 none (by omega) (by omega)) (by simp [dest,H])
      exact ⟨1,by omega,e⟩
    · have odd : 2*c+1=n := by omega
      have val : T (L+2*c+1)=some true := by
        dsimp only [T,D]; rw [digit fr (2*c) c (L+2*c+1) (by omega) (by omega)]
        simp only [show L+2*c < L+2*c+1 by omega,decide_true]
      have e := step_put (k := k) (P := P) 214 215 (L+2*c+1) H T (some false) .right
        (by omega) (by omega) (by omega) (by omega) (by rw [val]; exact row_value k 214 (some true) (by omega) (by omega)) (by change L+2*c+1+1=H; omega)
      rw [advance X L D (2*c) c (by dsimp [D]; omega),odd] at e
      have f := K (k := k) (P := P) 215 235 H (L+n) E none .left
        (by omega) (by omega) (by omega) (by omega) efr.right (row_value k 215 none (by omega) (by omega)) (by simp [dest,H])
      exact ⟨2,by omega,e.append f⟩
  obtain ⟨u,hu,rest⟩ := tail
  have d := sweepL (Cursor.q k 235) E L n
    (by simp only [Cursor.q,small_mod k 235 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; dsimp only [E,D]; rw [digit fr n c i lo (by omega)]; simp only [show ¬L+n < i by omega,decide_false]; exact row_value k 235 (some false) (by omega) (by omega))
  have e := K (k := k) (P := P) 235 236 L L E none .stay
    (by omega) (by omega) (by omega) (by omega) efr.sep (row_value k 235 none (by omega) (by omega)) rfl
  exact ⟨_,by omega,a.append b |>.append rest |>.append d |>.append e⟩
private theorem finish (k L n Q F r : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hr : 0 < r) :
    ∃ t, t ≤ 64*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k 213,L,data X L (F+r+2) (2*(n/2)) (n/2)⟩
      ⟨Cursor.q k 254,F+r+2,Target.image X L n F r⟩ := by
  let P := F+5*r+n+7
  let D := F+r+2
  let E := F+r+n+3
  let T := data X L D n (n/2)
  let V := put T (E+1) (some true)
  have room := fr.room
  have tf := travel fr n (n/2) le_rfl (by omega)
  obtain ⟨t,ht,pre⟩ := erase_finish k L n Q F r X fr
  obtain ⟨u,_,hu,out⟩ := outward2 k L n Q F r T tf
  have a := K (k := k) (P := P) 242 243 D (D+1) T none .right
    (by omega) (by omega) (by omega) (by omega) tf.d1 (row_value k 242 none (by omega) (by omega)) rfl
  have b := sweepR (Cursor.q k 243) T (D+1) n
    (by simp only [Cursor.q,small_mod k 243 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; obtain ⟨b,hb⟩ := tf.b1 i (by dsimp [D] at *; omega) (by dsimp [D] at *; omega); dsimp only [T,D]; rw [hb]; cases b <;> exact row_value k 243 _ (by omega) (by omega))
  rw [show D+1+n=E by omega] at b
  have c := K (k := k) (P := P) 243 244 E E T none .stay
    (by omega) (by omega) (by omega) (by omega) tf.d2 (row_value k 243 none (by omega) (by omega)) rfl
  have d := K (k := k) (P := P) 244 245 E (E+1) T none .right
    (by omega) (by omega) (by omega) (by omega) tf.d2 (row_value k 244 none (by omega) (by omega)) rfl
  have e := step_put (k := k) (P := P) 245 246 (E+1) E T (some true) .left
    (by omega) (by omega) (by omega) (by omega) (by rw [show T (E+1)=some false from tf.b2]; exact row_value k 245 (some false) (by omega) (by omega)) (by simp [dest])
  have old (i : Nat) (hi : i ≤ E) : V i=T i := by dsimp only [V,put]; rw [if_neg (by omega)]
  have f := K (k := k) (P := P) 246 248 E E V none .stay
    (by omega) (by omega) (by omega) (by omega) (by rw [old E le_rfl]; exact tf.d2) (row_value k 246 none (by omega) (by omega)) rfl
  have g := K (k := k) (P := P) 248 249 E (D+n) V none .left
    (by omega) (by omega) (by omega) (by omega) (by rw [old E le_rfl]; exact tf.d2) (row_value k 248 none (by omega) (by omega)) (by change E-1=D+n; dsimp [E,D]; omega)
  have h := sweepL (Cursor.q k 249) V D n
    (by simp only [Cursor.q,small_mod k 249 (by omega)]; omega) (P := P) (by omega)
    (by intro i lo hi; rw [old i (by dsimp [E,D] at *; omega)]; obtain ⟨b,hb⟩ := tf.b1 i (by dsimp [D] at *; omega) (by dsimp [D] at *; omega); dsimp only [T,D]; rw [hb]; cases b <;> exact row_value k 249 _ (by omega) (by omega))
  have j := K (k := k) (P := P) 249 254 D D V none .stay
    (by omega) (by omega) (by omega) (by omega) (by rw [old D (by dsimp [E,D]; omega)]; exact tf.d1) (row_value k 249 none (by omega) (by omega)) rfl
  have image : V=Target.image X L n F r := by
    funext i
    dsimp only [V,T,E,D,put,data,Target.image]
    split_ifs <;> first | rfl | omega
  have path := pre.append out |>.append a |>.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h |>.append j
  rw [image] at path
  exact ⟨_,by omega,path⟩
/-- Same literal Cursor table computes floor(n/2) and the first bitLength count. -/
theorem halve (k N B L n Q F r : Nat) (X : Nat → Option Bool)
    (hn : 2 ≤ n) (hr : 0 < r) (paid : 0 < Q) (room : L+n+1+Q < F)
    (sep : X L=none) (assn : ∀ i, L < i → i < L+n+1 → X i=some true)
    (right : X (L+n+1)=none)
    (marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → X i=some true)
    (gap : ∀ i, L+n+1+Q < i → i < F → X i=none)
    (fence : X F=some false) (d0 : X (F+1)=none)
    (b0 : ∀ i, F+1 < i → i < F+r+2 → X i=some true)
    (d1 : X (F+r+2)=none)
    (b1 : ∀ i, F+r+2 < i → i < F+r+n+3 → X i=some false)
    (d2 : X (F+r+n+3)=none) (b2 : X (F+r+n+4)=some false)
    (fit : F+5*r+n+7 < tapeLength N B) :
    ∃ t, t ≤ 128*(n+1)*(F+5*r+n+8) ∧
      (Cursor.machine k).run t (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)=
        ⟨Cursor.q k 254,⟨F+r+2,by omega⟩,fun i => Target.image X L n F r i.val⟩ ∧
      (∀ u, u < t → ((Cursor.machine k).run u
        (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 254) := by
  have fr : Frame X L n Q F r := ⟨paid,room,sep,assn,right,marks,gap,fence,d0,b0,d1,b1,d2,b2⟩
  obtain ⟨a,_,ha,pre⟩ := entry k L n Q F r X fr
  obtain ⟨b,_,hb,start⟩ := round k L n Q F r 0 X fr (by omega) true
  rw [data_zero] at start
  obtain ⟨c,hc,rest⟩ := iteration k L n Q F r 1 (n/2-1) X fr (by omega)
  rw [show 1+(n/2-1)=n/2 by omega] at rest
  obtain ⟨d,hd,post⟩ := finish k L n Q F r X fr hr
  have path := pre.append start |>.append rest |>.append post
  refine ⟨_,?_,path.execute fit,path.first fit⟩
  have hq : n/2-1+1 ≤ n := by omega
  have mul := Nat.mul_le_mul_right (64*(F+5*r+n+8)) hq
  nlinarith only [ha,hb,hc,hd,mul,Nat.zero_le (n*(F+5*r+n+8))]
end RuntimeBitLength
