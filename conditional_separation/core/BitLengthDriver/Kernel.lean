import BitLengthDriver.Rows
import Complexity.PrivateInterfaceLookupResolvedControl
namespace BitLengthDriver
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
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
  safe : c.state.val ≠ 250 ∧ c.state.val ≠ 304 ∧ c.state.val ≠ 308
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
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hs : s.val ≠ 250 ∧ s.val ≠ 304 ∧ s.val ≠ 308) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hs,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hs : s.val ≠ 250 ∧ s.val ≠ 304 ∧ s.val ≠ 308) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hs hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (hs : s.val ≠ 250 ∧ s.val ≠ 304 ∧ s.val ≠ 308) (fit : h+r   ≤   P) (rows : ∀ i, h   ≤   i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right hs (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (hs : s.val ≠ 250 ∧ s.val ≠ 304 ∧ s.val ≠ 308) (fit : low+r   ≤   P) (rows : ∀ i, low < i → i   ≤   low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left hs (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private theorem Path.first {k N B P t c d} (path : Path k P t c d) (hp : P < tapeLength N B)
    (u : Nat) (hu : u < t) :
    ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val ≠ 250 ∧
      ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val ≠ 304 ∧
      ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val ≠ 308 := by
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
private theorem row_value (k i : Nat) (b : Option Bool) (lo : 201 ≤ i) (hi : i < 308) :
    let code := (instructions k)[3*(i-201)+(match b with | none => 0 | some false => 1 | some true => 2)]!
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply phase_row k i _ b lo hi
  have len : (instructions k).length=321 := rfl
  have bound : 3*(i-201)+(match b with | none => 0 | some false => 1 | some true => 2) < (instructions k).length := by
    rw [len]; split <;> omega
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some]
  exact List.getElem?_eq_getElem bound
elab "literal" : tactic => withMainContext do
  let goal ← getMainGoal; let target ← Lean.Meta.whnf (← instantiateMVars (← goal.getType))
  unless target.isAppOfArity ``Eq 3 do throwError "literal expected equality"
  let args := target.getAppArgs[1]!.consumeMData.getAppArgs
  unless args.size=3 do throwError "literal expected UniformTM.step"
  let stateArgs := args[1]!.consumeMData.getAppArgs
  unless stateArgs.size=2 do throwError "literal expected Cursor.q"
  let rhs ← Lean.Meta.whnf target.getAppArgs[2]!; let qa := rhs.getAppArgs
  unless qa.size=4 do throwError "literal expected pair"
  let da := qa[2]!.consumeMData.getAppArgs
  unless da.size=2 do throwError "literal expected destination Cursor.q"
  let tail ← Lean.Meta.whnf qa[3]!; let ta := tail.getAppArgs
  unless ta.size=4 do throwError "literal expected symbol/move pair"
  let sym ← Lean.Meta.whnf ta[2]!; let tag ← if sym.isAppOf ``Option.none then pure 0 else do
    let ba ← Lean.Meta.whnf sym.getAppArgs.back!
    if ba.isConstOf ``Bool.true then pure 2 else if ba.isConstOf ``Bool.false then pure 1 else throwError "literal expected fixed symbol: {sym}"
  let mv ← Lean.Meta.whnf ta[3]!
  let move ← if mv.isConstOf ``Move.left then pure 0 else if mv.isConstOf ``Move.stay then pure 1 else if mv.isConstOf ``Move.right then pure 2 else throwError "literal expected fixed move"
  let dst ← Lean.Meta.withTransparency .all (Lean.Meta.whnf da[1]!); let src ← Lean.Meta.withTransparency .all (Lean.Meta.whnf stateArgs[1]!)
  let code ← Lean.Meta.mkAppM ``Nat.mul #[mkNatLit 9, dst]; let code ← Lean.Meta.mkAppM ``Nat.add #[code, mkNatLit (3*tag+move)]
  let term ← Lean.Meta.mkAppM ``phase_row #[stateArgs[0]!,src,code,args[2]!]; let goals ← goal.apply term
  replaceMainGoal goals
  evalTactic (← `(tactic| all_goals first | rfl | decide | (simp only [lab]; omega)))
private theorem K {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (mv : Move)
    (safe : s < 250 ∨ (254 ≤ s ∧ s < 304)) (hb : h ≤ P) (ha : h' ≤ P) (value : T h=b)
    (row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k d,b,mv)) (hm : dest h mv=h') :
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ := by
  apply keep _ _ _ _ _ _ ?_ hb ha (by rw [value]; exact row) hm
  simp only [Cursor.q,small_mod k s (by omega)]; omega
private structure Frame (X : Nat → Option Bool) (L n Q F r : Nat) : Prop where
  paid : 0 < Q
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
  b2 : ∀ i, F+r+n+3 < i → i < F+2*r+n+4 → X i=some false
  d3 : X (F+2*r+n+4)=none
private def img (X : Nat → Option Bool) (L n F r a0 a1 b0 b1 j : Nat) : Nat → Option Bool := fun i =>
  if L < i ∧ i < L+n+1 then some (decide (L+a0 < i ∧ i ≤ L+a1)) else
  if F+r+2 < i ∧ i < F+r+n+3 then some (decide (F+r+2+b0 < i ∧ i ≤ F+r+2+b1)) else
  if F+r+n+3 < i ∧ i < F+2*r+n+4 then some (decide (i ≤ F+r+n+3+j)) else X i
private def phase (X : Nat → Option Bool) (L n F r : Nat) (side : Bool) (v u c j : Nat) : Nat → Option Bool :=
  if side then img X L n F r u v 0 c j else img X L n F r 0 c u v j
private abbrev sh (side : Bool) (L F r : Nat) : Nat := if side then L else F+r+2
private abbrev lab (side : Bool) (a b : Nat) : Nat := if side then a else b
private theorem imgA {X L n Q F r} (_fr : Frame X L n Q F r) (a b c d j i : Nat)
    (lo : L < i) (hi : i < L+n+1) :
    img X L n F r a b c d j i=some (decide (L+a < i ∧ i ≤ L+b)) := by
  simp only [img]; rw [if_pos ⟨lo,hi⟩]
private theorem imgB {X L n Q F r} (fr : Frame X L n Q F r) (a b c d j i : Nat)
    (lo : F+r+2 < i) (hi : i < F+r+n+3) :
    img X L n F r a b c d j i=some (decide (F+r+2+c < i ∧ i ≤ F+r+2+d)) := by
  have h := fr.room; simp only [img]; rw [if_neg (by omega),if_pos ⟨lo,hi⟩]
private theorem imgC {X L n Q F r} (fr : Frame X L n Q F r) (a b c d j i : Nat)
    (lo : F+r+n+3 < i) (hi : i < F+2*r+n+4) :
    img X L n F r a b c d j i=some (decide (i ≤ F+r+n+3+j)) := by
  have h := fr.room; simp only [img]; rw [if_neg (by omega),if_neg (by omega),if_pos ⟨lo,hi⟩]
private theorem old {X L n Q F r} (_fr : Frame X L n Q F r) (a b c d j i : Nat)
    (ha : i ≤ L ∨ L+n+1 ≤ i) (hb : i ≤ F+r+2 ∨ F+r+n+3 ≤ i)
    (hc : i ≤ F+r+n+3 ∨ F+2*r+n+4 ≤ i) : img X L n F r a b c d j i=X i := by
  simp only [img]; rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
private structure Travel (T : Nat → Option Bool) (L n Q F r : Nat) : Prop where
  paid : 0 < Q
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
  b2 : ∀ i, F+r+n+3 < i → i < F+2*r+n+4 → ∃ b, T i=some b
  d3 : T (F+2*r+n+4)=none
private theorem travel {X L n Q F r} (fr : Frame X L n Q F r) (a b c d j : Nat) :
    Travel (img X L n F r a b c d j) L n Q F r := by
  have h := fr.room
  refine ⟨fr.paid,h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [old fr a b c d j L (by omega) (by omega) (by omega)]; exact fr.sep
  · intro i lo hi; exact ⟨_,imgA fr a b c d j i lo hi⟩
  · rw [old fr a b c d j (L+n+1) (by omega) (by omega) (by omega)]; exact fr.right
  · intro i lo hi; rw [old fr a b c d j i (by omega) (by omega) (by omega)]; exact fr.marks i lo hi
  · intro i lo hi; rw [old fr a b c d j i (by omega) (by omega) (by omega)]; exact fr.gap i lo hi
  · rw [old fr a b c d j F (by omega) (by omega) (by omega)]; exact fr.fence
  · rw [old fr a b c d j (F+1) (by omega) (by omega) (by omega)]; exact fr.d0
  · intro i lo hi; rw [old fr a b c d j i (by omega) (by omega) (by omega)]; exact fr.b0 i lo hi
  · rw [old fr a b c d j (F+r+2) (by omega) (by omega) (by omega)]; exact fr.d1
  · intro i lo hi; exact ⟨_,imgB fr a b c d j i lo hi⟩
  · rw [old fr a b c d j (F+r+n+3) (by omega) (by omega) (by omega)]; exact fr.d2
  · intro i lo hi; exact ⟨_,imgC fr a b c d j i lo hi⟩
  · rw [old fr a b c d j (F+2*r+n+4) (by omega) (by omega) (by omega)]; exact fr.d3
private theorem good (k s : Nat) (hs : s < 250 ∨ (254 ≤ s ∧ s < 304)) :
    (Cursor.q k s).val ≠ 250 ∧ (Cursor.q k s).val ≠ 304 ∧ (Cursor.q k s).val ≠ 308 := by
  simp only [Cursor.q,small_mod k s (by omega)]; omega
private theorem CR (k P s t d a w : Nat) (T : Nat → Option Bool) (fit : a+w+1 ≤ P)
    (left : T a=none) (right : T (a+w+1)=none)
    (occ : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (rs : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k t,none,.right))
    (rt : ∀ b, (Cursor.machine k).step (Cursor.q k t) (some b)=(Cursor.q k t,some b,.right))
    (rd : (Cursor.machine k).step (Cursor.q k t) none=(Cursor.q k d,none,.stay))
    (ss : s < 250 ∨ (254 ≤ s ∧ s < 304)) (st : t < 250 ∨ (254 ≤ t ∧ t < 304)) :
    Path k P (w+2) ⟨Cursor.q k s,a,T⟩ ⟨Cursor.q k d,a+w+1,T⟩ := by
  have x := K (k := k) (P := P) s t a (a+1) T none .right (by omega) (by omega) (by omega) left rs rfl
  have y := sweepR (Cursor.q k t) T (a+1) w (good k t st) (P := P) (by omega)
    (by intro i lo hi; obtain ⟨digit,hdigit⟩ := occ i (by omega) (by omega); rw [hdigit]; exact rt digit)
  rw [show a+1+w=a+w+1 by omega] at y
  have z := K (k := k) (P := P) t d (a+w+1) (a+w+1) T none .stay (by omega) fit fit right rd rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using x.append y |>.append z
private theorem CL (k P s t d a w : Nat) (T : Nat → Option Bool) (fit : a+w+1 ≤ P)
    (left : T a=none) (right : T (a+w+1)=none)
    (occ : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (rs : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k t,none,.left))
    (rt : ∀ b, (Cursor.machine k).step (Cursor.q k t) (some b)=(Cursor.q k t,some b,.left))
    (rd : (Cursor.machine k).step (Cursor.q k t) none=(Cursor.q k d,none,.stay))
    (ss : s < 250 ∨ (254 ≤ s ∧ s < 304)) (st : t < 250 ∨ (254 ≤ t ∧ t < 304)) :
    Path k P (w+2) ⟨Cursor.q k s,a+w+1,T⟩ ⟨Cursor.q k d,a,T⟩ := by
  have x := K (k := k) (P := P) s t (a+w+1) (a+w) T none .left (by omega) fit (by omega) right rs (by simp [dest])
  have y := sweepL (Cursor.q k t) T a w (good k t st) (P := P) (by omega)
    (by intro i lo hi; obtain ⟨digit,hdigit⟩ := occ i lo (by omega); rw [hdigit]; exact rt digit)
  have z := K (k := k) (P := P) t d a a T none .stay (by omega) (by omega) (by omega) left rd rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using x.append y |>.append z
private theorem FR (k P s t d L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r)
    (fit : F+1 ≤ P) (ss : s < 250 ∨ (254 ≤ s ∧ s < 304)) (st : t < 250 ∨ (254 ≤ t ∧ t < 304))
    (rs : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k t,none,.right))
    (rn : (Cursor.machine k).step (Cursor.q k t) none=(Cursor.q k t,none,.right))
    (rb : (Cursor.machine k).step (Cursor.q k t) (some true)=(Cursor.q k t,some true,.right))
    (rf : (Cursor.machine k).step (Cursor.q k t) (some false)=(Cursor.q k d,some false,.right)) :
    Path k P (F-(L+n+1)+1) ⟨Cursor.q k s,L+n+1,T⟩ ⟨Cursor.q k d,F+1,T⟩ := by
  have room := fr.room
  have x := K (k := k) (P := P) s t (L+n+1) (L+n+2) T none .right (by omega) (by omega) (by omega) fr.right rs rfl
  have y := sweepR (Cursor.q k t) T (L+n+2) (F-(L+n+1)-1) (good k t st) (P := P) (by omega) (by
    intro i lo hi; by_cases h : i ≤ L+n+1+Q
    · rw [fr.marks i (by omega) h]; exact rb
    · rw [fr.gap i (by omega) (by omega)]; exact rn)
  rw [show L+n+2+(F-(L+n+1)-1)=F by omega] at y
  have z := K (k := k) (P := P) t d F (F+1) T (some false) .right (by omega) (by omega) fit fr.fence rf rfl
  convert x.append y |>.append z using 1; omega
private theorem FL (k P s t gap marks d L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r)
    (fit : F+1 ≤ P) (ss : ∀ i ∈ [s,t,gap,marks], i < 250 ∨ (254 ≤ i ∧ i < 304))
    (rs : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k t,none,.left))
    (rt : (Cursor.machine k).step (Cursor.q k t) (some false)=(Cursor.q k gap,some false,.left))
    (rn : (Cursor.machine k).step (Cursor.q k gap) none=(Cursor.q k gap,none,.left))
    (rb : (Cursor.machine k).step (Cursor.q k gap) (some true)=(Cursor.q k marks,some true,.left))
    (rm : (Cursor.machine k).step (Cursor.q k marks) (some true)=(Cursor.q k marks,some true,.left))
    (rd : (Cursor.machine k).step (Cursor.q k marks) none=(Cursor.q k d,none,.stay)) :
    Path k P (F-(L+n+1)+2) ⟨Cursor.q k s,F+1,T⟩ ⟨Cursor.q k d,L+n+1,T⟩ := by
  have room := fr.room; have paid := fr.paid
  have gs := good k s (ss s (by simp)); have gt := good k t (ss t (by simp))
  have gg := good k gap (ss gap (by simp)); have gm := good k marks (ss marks (by simp))
  have x := K (k := k) (P := P) s t (F+1) F T none .left (by have h := ss s (by simp); omega) fit (by omega) fr.d0 rs (by simp [dest])
  have y := K (k := k) (P := P) t gap F (F-1) T (some false) .left (by have h := ss t (by simp); omega) (by omega) (by omega) fr.fence rt rfl
  have z := sweepL (Cursor.q k gap) T (L+n+1+Q) (F-(L+n+1+Q)-1) gg (P := P) (by omega)
    (by intro i lo hi; rw [fr.gap i (by omega) (by omega)]; exact rn)
  rw [show L+n+1+Q+(F-(L+n+1+Q)-1)=F-1 by omega] at z
  have a := K (k := k) (P := P) gap marks (L+n+1+Q) (L+n+1+(Q-1)) T (some true) .left
    (by have h := ss gap (by simp); omega) (by omega) (by omega) (fr.marks _ (by omega) le_rfl) rb (by change L+n+1+Q-1=L+n+1+(Q-1); omega)
  have b := sweepL (Cursor.q k marks) T (L+n+1) (Q-1) gm (P := P) (by omega)
    (by intro i lo hi; rw [fr.marks i lo (by omega)]; exact rm)
  have c := K (k := k) (P := P) marks d (L+n+1) (L+n+1) T none .stay (by have h := ss marks (by simp); omega) (by omega) (by omega) fr.right rd rfl
  convert x.append y |>.append z |>.append a |>.append b |>.append c using 1; omega
private theorem outA (k L n Q F r : Nat) (T : Nat → Option Bool) (frame : Travel T L n Q F r) :
    Path k (F+5*r+n+7) (F-L+r+4) ⟨Cursor.q k 217,L,T⟩ ⟨Cursor.q k 223,F+r+2,T⟩ := by
  let P := F+5*r+n+7; have room := frame.room
  have a := CR k P 217 218 219 (L) n T (by omega) (frame.sep) (frame.right) (frame.assn) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  have b := FR k P 219 220 221 L n Q F r T frame (by omega) (by omega) (by omega) (by literal) (by literal) (by literal) (by literal)
  have c := CR k P 221 222 223 (F+1) r T (by omega) (frame.d0) (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.d1) (by intro i lo hi; exact ⟨true,frame.b0 i lo (by omega)⟩) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  rw [show F+1+r+1=F+r+2 by omega] at c
  convert a.append b |>.append c using 1; omega
private theorem returnB (k L n Q F r : Nat) (T : Nat → Option Bool) (frame : Travel T L n Q F r) :
    Path k (F+5*r+n+7) (F-L+r+4) ⟨Cursor.q k 281,L,T⟩ ⟨Cursor.q k 265,F+r+2,T⟩ := by
  let P := F+5*r+n+7; have room := frame.room
  have a := CR k P 281 282 283 (L) n T (by omega) (frame.sep) (frame.right) (frame.assn) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  have b := FR k P 283 284 285 L n Q F r T frame (by omega) (by omega) (by omega) (by literal) (by literal) (by literal) (by literal)
  have c := CR k P 285 286 265 (F+1) r T (by omega) (frame.d0) (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.d1) (by intro i lo hi; exact ⟨true,frame.b0 i lo (by omega)⟩) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  rw [show F+1+r+1=F+r+2 by omega] at c
  convert a.append b |>.append c using 1; omega
private theorem toC_A (k L n Q F r : Nat) (T : Nat → Option Bool) (frame : Travel T L n Q F r) :
    Path k (F+5*r+n+7) (F-L+r+4) ⟨Cursor.q k 236,L,T⟩ ⟨Cursor.q k 242,F+r+2,T⟩ := by
  let P := F+5*r+n+7; have room := frame.room
  have a := CR k P 236 237 238 (L) n T (by omega) (frame.sep) (frame.right) (frame.assn) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  have b := FR k P 238 239 240 L n Q F r T frame (by omega) (by omega) (by omega) (by literal) (by literal) (by literal) (by literal)
  have c := CR k P 240 241 242 (F+1) r T (by omega) (frame.d0) (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.d1) (by intro i lo hi; exact ⟨true,frame.b0 i lo (by omega)⟩) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  rw [show F+1+r+1=F+r+2 by omega] at c
  convert a.append b |>.append c using 1; omega
private theorem outB (k L n Q F r : Nat) (T : Nat → Option Bool) (frame : Travel T L n Q F r) :
    Path k (F+5*r+n+7) (F-L+r+5) ⟨Cursor.q k 269,F+r+2,T⟩ ⟨Cursor.q k 277,L,T⟩ := by
  let P := F+5*r+n+7; have room := frame.room
  have a := CL k P 269 270 271 (F+1) r T (by omega) (frame.d0) (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.d1) (by intro i lo hi; exact ⟨true,frame.b0 i lo (by omega)⟩) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  rw [show F+1+r+1=F+r+2 by omega] at a
  have b := FL k P 271 272 273 274 275 L n Q F r T frame (by omega) (by intro i hi; simp at hi; omega) (by literal) (by literal) (by literal) (by literal) (by literal) (by literal)
  have c := CL k P 275 276 277 (L) n T (by omega) (frame.sep) (frame.right) (frame.assn) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  convert a.append b |>.append c using 1; omega
private theorem returnA (k L n Q F r : Nat) (T : Nat → Option Bool) (frame : Travel T L n Q F r) :
    Path k (F+5*r+n+7) (F-L+r+5) ⟨Cursor.q k 227,F+r+2,T⟩ ⟨Cursor.q k 213,L,T⟩ := by
  let P := F+5*r+n+7; have room := frame.room
  have a := CL k P 227 228 229 (F+1) r T (by omega) (frame.d0) (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.d1) (by intro i lo hi; exact ⟨true,frame.b0 i lo (by omega)⟩) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  rw [show F+1+r+1=F+r+2 by omega] at a
  have b := FL k P 229 230 231 232 233 L n Q F r T frame (by omega) (by intro i hi; simp at hi; omega) (by literal) (by literal) (by literal) (by literal) (by literal) (by literal)
  have c := CL k P 233 234 213 (L) n T (by omega) (frame.sep) (frame.right) (frame.assn) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  convert a.append b |>.append c using 1; omega
private theorem emptyB (k L n Q F r : Nat) (T : Nat → Option Bool) (frame : Travel T L n Q F r) :
    Path k (F+5*r+n+7) (F-L+r+5) ⟨Cursor.q k 257,F+r+2,T⟩ ⟨Cursor.q k 308,L,T⟩ := by
  let P := F+5*r+n+7; have room := frame.room
  have a := CL k P 257 258 259 (F+1) r T (by omega) (frame.d0) (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.d1) (by intro i lo hi; exact ⟨true,frame.b0 i lo (by omega)⟩) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  rw [show F+1+r+1=F+r+2 by omega] at a
  have b := FL k P 259 260 261 262 263 L n Q F r T frame (by omega) (by intro i hi; simp at hi; omega) (by literal) (by literal) (by literal) (by literal) (by literal) (by literal)
  have c := CL k P 263 264 308 (L) n T (by omega) (frame.sep) (frame.right) (frame.assn) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  convert a.append b |>.append c using 1; omega
private theorem fromC_B (k L n Q F r : Nat) (T : Nat → Option Bool) (frame : Travel T L n Q F r) :
    Path k (F+5*r+n+7) (F-L+r+5) ⟨Cursor.q k 296,F+r+2,T⟩ ⟨Cursor.q k 209,L,T⟩ := by
  let P := F+5*r+n+7; have room := frame.room
  have a := CL k P 296 297 298 (F+1) r T (by omega) (frame.d0) (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using frame.d1) (by intro i lo hi; exact ⟨true,frame.b0 i lo (by omega)⟩) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  rw [show F+1+r+1=F+r+2 by omega] at a
  have b := FL k P 298 299 300 301 302 L n Q F r T frame (by omega) (by intro i hi; simp at hi; omega) (by literal) (by literal) (by literal) (by literal) (by literal) (by literal)
  have c := CL k P 302 303 209 (L) n T (by omega) (frame.sep) (frame.right) (frame.assn) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
  convert a.append b |>.append c using 1; omega
private theorem pTravel {X L n Q F r} (fr : Frame X L n Q F r) (side : Bool) (v u c j : Nat) :
    Travel (phase X L n F r side v u c j) L n Q F r := by
  cases side
  · exact travel fr 0 c u v j
  · exact travel fr u v 0 c j
private theorem srcNone {T L n Q F r} (fr : Travel T L n Q F r) (side : Bool) : T (sh side L F r)=none := by
  cases side
  · exact fr.d1
  · exact fr.sep
private theorem srcEnd {T L n Q F r} (fr : Travel T L n Q F r) (side : Bool) : T (sh side L F r+n+1)=none := by
  cases side
  · simpa [sh,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fr.d2
  · exact fr.right
private theorem srcOcc {T L n Q F r} (fr : Travel T L n Q F r) (side : Bool) (i : Nat)
    (lo : sh side L F r < i) (hi : i < sh side L F r+n+1) : ∃ b, T i=some b := by
  cases side
  · change F+r+2 < i at lo; change i < F+r+2+n+1 at hi
    exact fr.b1 i lo (by omega)
  · exact fr.assn i lo hi
private theorem srcDigit {X L n Q F r} (fr : Frame X L n Q F r) (side : Bool) (v u c j i : Nat)
    (lo : sh side L F r < i) (hi : i < sh side L F r+n+1) :
    phase X L n F r side v u c j i=some (decide (sh side L F r+u < i ∧ i ≤ sh side L F r+v)) := by
  cases side
  · change i < F+r+2+n+1 at hi
    exact imgB fr 0 c u v j i lo (by omega)
  · exact imgA fr u v 0 c j i lo hi
private theorem dstDigit {X L n Q F r} (fr : Frame X L n Q F r) (side : Bool) (v u c j i : Nat)
    (lo : sh (!side) L F r < i) (hi : i < sh (!side) L F r+n+1) :
    phase X L n F r side v u c j i=some (decide (i ≤ sh (!side) L F r+c)) := by
  cases side
  · change L < i at lo; change i < L+n+1 at hi
    change img X L n F r 0 c u v j i=some (decide (i ≤ L+c))
    rw [imgA fr 0 c u v j i lo hi]; simp only [Nat.add_zero,lo,true_and]
  · change F+r+2 < i at lo; change i < F+r+2+n+1 at hi
    change img X L n F r u v 0 c j i=some (decide (i ≤ F+r+2+c))
    rw [imgB fr u v 0 c j i lo (by omega)]; simp only [Nat.add_zero,lo,true_and]
private theorem put_ext (T U : Nat → Option Bool) (h : Nat) (b : Option Bool)
    (atCell : U h=b) (away : ∀ i, i ≠ h → U i=T i) : put T h b=U := by
  funext i; by_cases hi : i=h
  · subst i; simpa only [put,ite_true] using atCell.symm
  · simp only [put,if_neg hi]; exact (away i hi).symm
private theorem advanceSrc {X L n Q F r} (fr : Frame X L n Q F r) (side : Bool) (v u c j : Nat)
    (hu : u < v) (hv : v ≤ n) :
    put (phase X L n F r side v u c j) (sh side L F r+u+1) (some false)=phase X L n F r side v (u+1) c j := by
  apply put_ext
  · rw [srcDigit fr side v (u+1) c j (sh side L F r+u+1) (by omega) (by omega),decide_eq_false (by omega)]
  · intro i hi; cases side <;> simp [sh] at hi <;> simp only [phase, Bool.false_eq_true,  ite_false, ite_true] <;> unfold img <;> split_ifs <;> first | rfl | (first | omega | (apply congrArg some; apply decide_eq_decide.mpr; omega))
private theorem advanceDst {X L n Q F r} (fr : Frame X L n Q F r) (side : Bool) (v u c j : Nat)
    (hc : c < n) :
    put (phase X L n F r side v u c j) (sh (!side) L F r+c+1) (some true)=phase X L n F r side v u (c+1) j := by
  apply put_ext
  · rw [dstDigit fr side v u (c+1) j (sh (!side) L F r+c+1) (by omega) (by omega),decide_eq_true (by omega)]
  · intro i hi; cases side <;> simp [sh] at hi <;> simp only [phase, Bool.false_eq_true,  ite_false, ite_true] <;> unfold img <;> split_ifs <;> first | rfl | (first | omega | (apply congrArg some; apply decide_eq_decide.mpr; omega))
private theorem advanceOut {X L n Q F r} (fr : Frame X L n Q F r) (side : Bool) (v u c j : Nat)
    (hj : j < r) :
    put (phase X L n F r side v u c j) (F+r+n+3+j+1) (some true)=phase X L n F r side v u c (j+1) := by
  apply put_ext
  · cases side
    · rw [show phase X L n F r false v u c (j+1) (F+r+n+3+j+1)=some (decide (F+r+n+3+j+1 ≤ F+r+n+3+(j+1))) from imgC fr 0 c u v (j+1) _ (by omega) (by omega),decide_eq_true (by omega)]
    · rw [show phase X L n F r true v u c (j+1) (F+r+n+3+j+1)=some (decide (F+r+n+3+j+1 ≤ F+r+n+3+(j+1))) from imgC fr u v 0 c (j+1) _ (by omega) (by omega),decide_eq_true (by omega)]
  · intro i hi; cases side <;> simp only [phase, Bool.false_eq_true,  ite_false, ite_true] <;> unfold img <;> split_ifs <;> first | rfl | (first | omega | (apply congrArg some; apply decide_eq_decide.mpr; omega))
private theorem turn (X : Nat → Option Bool) (L n F r : Nat) (side : Bool) (v c j : Nat) :
    phase X L n F r side v v c j=phase X L n F r (!side) c 0 0 j := by
  cases side <;> funext i <;> simp only [phase, Bool.false_eq_true,  Bool.not_false, Bool.not_true, ite_false, ite_true] <;> unfold img <;> split_ifs <;> first | rfl | (first | omega | (apply congrArg some; apply decide_eq_decide.mpr; omega))
private theorem routeOut (k L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r) (side : Bool) :
    ∃ t, t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 217 269),sh side L F r,T⟩ ⟨Cursor.q k (lab side 223 277),sh (!side) L F r,T⟩ := by
  have h := fr.room
  cases side
  · exact ⟨_,by omega,outB k L n Q F r T fr⟩
  · exact ⟨_,by omega,outA k L n Q F r T fr⟩
private theorem routeReturn (k L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r) (side : Bool) :
    ∃ t, t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 227 281),sh (!side) L F r,T⟩ ⟨Cursor.q k (lab side 213 265),sh side L F r,T⟩ := by
  have h := fr.room
  cases side
  · exact ⟨_,by omega,returnB k L n Q F r T fr⟩
  · exact ⟨_,by omega,returnA k L n Q F r T fr⟩
private theorem W {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (b out : Option Bool) (mv : Move)
    (valid : s < 250 ∨ (254 ≤ s ∧ s < 304)) (hb : h ≤ P) (ha : h' ≤ P) (value : T h=b)
    (row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k d,out,mv)) (hm : dest h mv=h') :
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',put T h out⟩ :=
  hop _ _ _ _ _ _ _ (good k s valid) hb ha (by rw [value]; exact row) hm
private theorem erasePair (k L n Q F r v c j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hv : v ≤ n) (hc : c < v/2) (side first : Bool) :
    Path k (F+5*r+n+7) (4*c+5)
      ⟨Cursor.q k (if first then lab side 209 254 else lab side 213 265),sh side L F r,phase X L n F r side v (2*c) c j⟩
      ⟨Cursor.q k (lab side 217 269),sh side L F r,phase X L n F r side v (2*c+2) c j⟩ := by
  let P := F+5*r+n+7; let S := sh side L F r
  let seek := if first then lab side 210 255 else lab side 214 266
  let start := if first then lab side 209 254 else lab side 213 265
  let T := phase X L n F r side v (2*c) c j
  let V := phase X L n F r side v (2*c+1) c j
  let E := phase X L n F r side v (2*c+2) c j
  have room := fr.room; have hcv : 2*c+2 ≤ v := by omega
  have sf : S+n+1 ≤ P := by cases side <;> simp [S,sh,P] <;> omega
  have ts := srcNone (pTravel fr side v (2*c) c j) side
  have a := K (k := k) (P := P) start seek S (S+1) T none .right
    (by cases side <;> cases first <;> decide) (by omega) (by omega) ts
    (by cases side <;> cases first <;> literal) rfl
  have b := sweepR (Cursor.q k seek) T (S+1) (2*c) (good k seek (by cases side <;> cases first <;> decide)) (P := P) (by omega) (by
    intro i lo hi
    have val : T i=some false := by
      change phase X L n F r side v (2*c) c j i=_
      rw [srcDigit fr side v (2*c) c j i (by omega) (by omega),decide_eq_false (by change ¬(S+2*c < i ∧ i ≤ S+v); omega)]
    rw [val]; cases side <;> cases first <;> literal)
  rw [show S+1+2*c=S+2*c+1 by omega] at b
  have one : T (S+2*c+1)=some true := by
    change phase X L n F r side v (2*c) c j (S+2*c+1)=_
    rw [srcDigit fr side v (2*c) c j _ (by omega) (by omega),decide_eq_true (by change S+2*c < S+2*c+1 ∧ S+2*c+1 ≤ S+v; omega)]
  have d := W (k := k) (P := P) seek (lab side 215 267) (S+2*c+1) (S+2*c+2) T (some true) (some false) .right
    (by cases side <;> cases first <;> decide) (by omega) (by omega) one (by cases side <;> cases first <;> literal) rfl
  have de : put T (S+2*c+1) (some false)=V := advanceSrc fr side v (2*c) c j (by omega) hv
  rw [de] at d
  have two : V (S+2*c+2)=some true := by
    change phase X L n F r side v (2*c+1) c j (S+2*c+2)=_
    rw [srcDigit fr side v (2*c+1) c j _ (by omega) (by omega),decide_eq_true (by change S+(2*c+1) < S+2*c+2 ∧ S+2*c+2 ≤ S+v; omega)]
  have e := W (k := k) (P := P) (lab side 215 267) (lab side 216 268) (S+2*c+2) (S+2*c+1) V (some true) (some false) .left
    (by cases side <;> decide) (by omega) (by omega) two (by cases side <;> literal) (by change S+2*c+2-1=S+2*c+1; omega)
  have ee : put V (S+2*c+2) (some false)=E := by
    simpa only [Nat.add_assoc] using advanceSrc fr side v (2*c+1) c j (by omega) hv
  rw [ee] at e
  have ef : Travel E L n Q F r := pTravel fr side v (2*c+2) c j
  have f := sweepL (Cursor.q k (lab side 216 268)) E S (2*c+1) (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
    intro i lo hi; obtain ⟨digit,hdigit⟩ := srcOcc ef side i lo (by omega); rw [hdigit]; cases side <;> cases digit <;> literal)
  have g := K (k := k) (P := P) (lab side 216 268) (lab side 217 269) S S E none .stay
    (by cases side <;> decide) (by omega) (by omega) (srcNone ef side) (by cases side <;> literal) rfl
  convert a.append b |>.append d |>.append e |>.append f |>.append g using 1; omega
private theorem appendPair (k L n Q F r v c j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hv : v ≤ n) (hc : c < v/2) (side : Bool) :
    Path k (F+5*r+n+7) (2*c+3)
      ⟨Cursor.q k (lab side 223 277),sh (!side) L F r,phase X L n F r side v (2*c+2) c j⟩
      ⟨Cursor.q k (lab side 227 281),sh (!side) L F r,phase X L n F r side v (2*c+2) (c+1) j⟩ := by
  let P := F+5*r+n+7; let D := sh (!side) L F r
  let E := phase X L n F r side v (2*c+2) c j
  let Z := phase X L n F r side v (2*c+2) (c+1) j
  have room := fr.room; have hcv : 2*c+2 ≤ v := by omega
  have df : D+n+1 ≤ P := by cases side <;> simp [D,sh,P] <;> omega
  have ef : Travel E L n Q F r := pTravel fr side v (2*c+2) c j
  have h := K (k := k) (P := P) (lab side 223 277) (lab side 224 278) D (D+1) E none .right
    (by cases side <;> decide) (by omega) (by omega) (srcNone ef (!side)) (by cases side <;> literal) rfl
  have ii := sweepR (Cursor.q k (lab side 224 278)) E (D+1) c (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
    intro i lo hi
    have val : E i=some true := by
      change phase X L n F r side v (2*c+2) c j i=_
      rw [dstDigit fr side v (2*c+2) c j i (by omega) (by omega),decide_eq_true (by change i ≤ D+c; omega)]
    rw [val]; cases side <;> literal)
  rw [show D+1+c=D+c+1 by omega] at ii
  have zero : E (D+c+1)=some false := by
    change phase X L n F r side v (2*c+2) c j (D+c+1)=_
    rw [dstDigit fr side v (2*c+2) c j _ (by omega) (by omega),decide_eq_false (by change ¬D+c+1 ≤ D+c; omega)]
  have jj := W (k := k) (P := P) (lab side 224 278) (lab side 225 279) (D+c+1) (D+c) E (some false) (some true) .left
    (by cases side <;> decide) (by omega) (by omega) zero (by cases side <;> literal) (by change D+c+1-1=D+c; omega)
  have je : put E (D+c+1) (some true)=Z := advanceDst fr side v (2*c+2) c j (by omega)
  rw [je] at jj
  have zf : Travel Z L n Q F r := pTravel fr side v (2*c+2) (c+1) j
  have kk := sweepL (Cursor.q k (lab side 225 279)) Z D c (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
    intro i lo hi; obtain ⟨digit,hdigit⟩ := srcOcc zf (!side) i lo (by omega); rw [hdigit]; cases side <;> cases digit <;> literal)
  have ll := K (k := k) (P := P) (lab side 225 279) (lab side 227 281) D D Z none .stay
    (by cases side <;> decide) (by omega) (by omega) (srcNone zf (!side)) (by cases side <;> literal) rfl
  convert h.append ii |>.append jj |>.append kk |>.append ll using 1; omega
private theorem pair (k L n Q F r v c j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hv : v ≤ n) (hc : c < v/2) (side first : Bool) :
    ∃ t, t ≤ 64*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (if first then lab side 209 254 else lab side 213 265),sh side L F r,phase X L n F r side v (2*c) c j⟩
      ⟨Cursor.q k (lab side 213 265),sh side L F r,phase X L n F r side v (2*(c+1)) (c+1) j⟩ := by
  have a := erasePair k L n Q F r v c j X fr hv hc side first
  obtain ⟨u,hu,b⟩ := routeOut k L n Q F r _ (pTravel fr side v (2*c+2) c j) side
  have d := appendPair k L n Q F r v c j X fr hv hc side
  obtain ⟨w,hw,e⟩ := routeReturn k L n Q F r _ (pTravel fr side v (2*c+2) (c+1) j) side
  have path := a.append b |>.append d |>.append e
  rw [show 2*c+2=2*(c+1) by omega] at path
  refine ⟨_,?_,path⟩
  have h := fr.room
  have cs : c ≤ n := by omega
  omega
private theorem pairs (k L n Q F r v c d j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hv : v ≤ n) (hc : c+d ≤ v/2) (side : Bool) :
    ∃ t, t ≤ d*(64*(F+5*r+n+8)) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 213 265),sh side L F r,phase X L n F r side v (2*c) c j⟩
      ⟨Cursor.q k (lab side 213 265),sh side L F r,phase X L n F r side v (2*(c+d)) (c+d) j⟩ := by
  induction d generalizing c with
  | zero =>
    have hp : sh side L F r ≤ F+5*r+n+7 := by have h := fr.room; cases side <;> simp only [sh,Bool.false_eq_true,ite_false,ite_true] <;> omega
    exact ⟨0,by omega,by simpa using Path.nil ⟨Cursor.q k (lab side 213 265),sh side L F r,phase X L n F r side v (2*c) c j⟩ hp⟩
  | succ d ih =>
    obtain ⟨t,ht,a⟩ := pair k L n Q F r v c j X fr hv (by omega) side false
    obtain ⟨u,hu,b⟩ := ih (c+1) (by omega)
    exact ⟨t+u,by nlinarith only [ht,hu],by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b⟩
private theorem finishClear (k L n Q F r v j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (vp : 0 < v) (hv : v ≤ n) (side first : Bool)
    (hf : first=true → v/2=0) :
    ∃ t, t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (if first then lab side 209 254 else lab side 213 265),sh side L F r,phase X L n F r side v (2*(v/2)) (v/2) j⟩
      ⟨Cursor.q k (lab side 236 288),sh side L F r,phase X L n F r side v v (v/2) j⟩ := by
  let P := F+5*r+n+7; let S := sh side L F r; let c := v/2
  let start := if first then lab side 209 254 else lab side 213 265
  let seek := if first then lab side 210 255 else lab side 214 266
  let T := phase X L n F r side v (2*c) c j
  let E := phase X L n F r side v v c j
  have room := fr.room
  have sf : S+n+1 ≤ P := by cases side <;> simp [S,sh,P] <;> omega
  have ef : Travel E L n Q F r := pTravel fr side v v c j
  have a := K (k := k) (P := P) start seek S (S+1) T none .right
    (by cases side <;> cases first <;> decide) (by omega) (by omega) (srcNone (pTravel fr side v (2*c) c j) side)
    (by cases side <;> cases first <;> literal) rfl
  have tail : ∃ t, t ≤ 2*n+2 ∧ Path k P t ⟨Cursor.q k seek,S+1,T⟩ ⟨Cursor.q k (lab side 236 288),S,E⟩ := by
    by_cases even : 2*c=v
    · have ff : first=false := by
        cases first
        · rfl
        · have h := hf rfl
          dsimp only [c] at even
          omega
      subst first
      have same : T=E := by dsimp only [T,E]; rw [even]
      rw [same]
      have b := sweepR (Cursor.q k seek) E (S+1) n (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
        intro i lo hi
        have val : E i=some false := by
          change phase X L n F r side v v c j i=_
          rw [srcDigit fr side v v c j i (by omega) (by omega),decide_eq_false (by omega)]
        rw [val]; cases side <;> literal)
      rw [show S+1+n=S+n+1 by omega] at b
      have d := K (k := k) (P := P) seek (lab side 235 287) (S+n+1) (S+n) E none .left
        (by cases side <;> decide) (by omega) (by omega) (srcEnd ef side) (by cases side <;> literal) (by simp [dest])
      have e := sweepL (Cursor.q k (lab side 235 287)) E S n (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
        intro i lo hi; obtain ⟨digit,hdigit⟩ := srcOcc ef side i lo (by omega); rw [hdigit]; cases side <;> cases digit <;> literal)
      have f := K (k := k) (P := P) (lab side 235 287) (lab side 236 288) S S E none .stay
        (by cases side <;> decide) (by omega) (by omega) (srcNone ef side) (by cases side <;> literal) rfl
      exact ⟨_,by omega,b.append d |>.append e |>.append f⟩
    · have odd : 2*c+1=v := by dsimp [c] at *; omega
      have b := sweepR (Cursor.q k seek) T (S+1) (2*c) (good k _ (by cases side <;> cases first <;> decide)) (P := P) (by omega) (by
        intro i lo hi
        have val : T i=some false := by
          change phase X L n F r side v (2*c) c j i=_
          rw [srcDigit fr side v (2*c) c j i (by omega) (by omega),decide_eq_false (by omega)]
        rw [val]; cases side <;> cases first <;> literal)
      rw [show S+1+2*c=S+v by omega] at b
      have val : T (S+v)=some true := by
        change phase X L n F r side v (2*c) c j (S+v)=_
        rw [srcDigit fr side v (2*c) c j _ (by omega) (by omega),decide_eq_true (by omega)]
      have d := W (k := k) (P := P) seek (lab side 215 267) (S+v) (S+v+1) T (some true) (some false) .right
        (by cases side <;> cases first <;> decide) (by omega) (by omega) val (by cases side <;> cases first <;> literal) rfl
      have same : put T (S+v) (some false)=E := by simpa only [Nat.add_assoc,odd] using advanceSrc fr side v (2*c) c j (by omega) hv
      rw [same] at d
      have e := K (k := k) (P := P) (lab side 215 267) (lab side 235 287) (S+v+1) (S+v) E (E (S+v+1)) .left
        (by cases side <;> decide) (by omega) (by omega) rfl (by
          by_cases eq : v=n
          · rw [eq,srcEnd ef side]; cases side <;> literal
          · have ve : E (S+v+1)=some false := by
              change phase X L n F r side v v c j (S+v+1)=_
              rw [srcDigit fr side v v c j _ (by omega) (by omega),decide_eq_false (by omega)]
            rw [ve]; cases side <;> literal) (by simp [dest])
      have f := sweepL (Cursor.q k (lab side 235 287)) E S v (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
        intro i lo hi; obtain ⟨digit,hdigit⟩ := srcOcc ef side i lo (by omega); rw [hdigit]; cases side <;> cases digit <;> literal)
      have g := K (k := k) (P := P) (lab side 235 287) (lab side 236 288) S S E none .stay
        (by cases side <;> decide) (by omega) (by omega) (srcNone ef side) (by cases side <;> literal) rfl
      exact ⟨_,by omega,b.append d |>.append e |>.append f |>.append g⟩
  obtain ⟨u,hu,rest⟩ := tail
  exact ⟨_,by omega,a.append rest⟩
private theorem toCounter (k L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r) (side : Bool) :
    ∃ t, t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 236 288),sh side L F r,T⟩ ⟨Cursor.q k (lab side 244 290),F+r+n+3,T⟩ := by
  let P := F+5*r+n+7; have room := fr.room
  cases side
  · have a := CR k P 288 289 290 (F+r+2) n T (by omega) fr.d1 (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fr.d2)
      (by intro i lo hi; exact fr.b1 i lo (by omega)) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
    rw [show F+r+2+n+1=F+r+n+3 by omega] at a
    exact ⟨_,by omega,a⟩
  · have a := toC_A k L n Q F r T fr
    have b := CR k P 242 243 244 (F+r+2) n T (by omega) fr.d1 (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fr.d2)
      (by intro i lo hi; exact fr.b1 i lo (by omega)) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
    rw [show F+r+2+n+1=F+r+n+3 by omega] at b
    exact ⟨_,by omega,a.append b⟩
private theorem halfToCounter (k L n Q F r v j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (vp : 0 < v) (hv : v ≤ n) (side : Bool) :
    ∃ t, t ≤ 96*(v+1)*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 209 254),sh side L F r,phase X L n F r side v 0 0 j⟩
      ⟨Cursor.q k (lab side 244 290),F+r+n+3,phase X L n F r side v v (v/2) j⟩ := by
  have room := fr.room
  have segment : ∃ t, t ≤ (v/2)*(64*(F+5*r+n+8))+16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 209 254),sh side L F r,phase X L n F r side v 0 0 j⟩
      ⟨Cursor.q k (lab side 236 288),sh side L F r,phase X L n F r side v v (v/2) j⟩ := by
    by_cases hz : v/2=0
    · obtain ⟨t,ht,done⟩ := finishClear k L n Q F r v j X fr vp hv side true (by intro _; exact hz)
      rw [hz] at done
      exact ⟨t,by omega,by simpa [hz] using done⟩
    · obtain ⟨t,ht,a⟩ := pair k L n Q F r v 0 j X fr hv (by omega) side true
      obtain ⟨u,hu,b⟩ := pairs k L n Q F r v 1 (v/2-1) j X fr hv (by omega) side
      rw [show 1+(v/2-1)=v/2 by omega] at b
      obtain ⟨w,hw,d⟩ := finishClear k L n Q F r v j X fr vp hv side false (by intro h; cases h)
      have cost := congrArg (fun q => q*(64*(F+5*r+n+8))) (show (v/2-1)+1=v/2 by omega)
      exact ⟨t+u+w,by nlinarith only [ht,hu,hw,cost],by simpa using a.append b |>.append d⟩
  obtain ⟨t,ht,a⟩ := segment
  obtain ⟨u,hu,b⟩ := toCounter k L n Q F r _ (pTravel fr side v v (v/2) j) side
  exact ⟨t+u,by have hd := Nat.mul_le_mul_right (64*(F+5*r+n+8)) (show v/2 ≤ v by omega); nlinarith only [ht,hu,hd,Nat.zero_le (v*(F+5*r+n+8))],a.append b⟩
private theorem outDigit {X L n Q F r} (fr : Frame X L n Q F r) (side : Bool) (v u c j i : Nat)
    (lo : F+r+n+3 < i) (hi : i < F+2*r+n+4) :
    phase X L n F r side v u c j i=some (decide (i ≤ F+r+n+3+j)) := by
  cases side
  · exact imgC fr 0 c u v j i lo hi
  · exact imgC fr u v 0 c j i lo hi
private theorem increment (k L n Q F r v c j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (hj : j ≤ r) (side : Bool) :
    Path k (F+5*r+n+7) (2*j+3)
      ⟨Cursor.q k (lab side 244 290),F+r+n+3,phase X L n F r side v v c j⟩
      ⟨Cursor.q k (if j < r then lab side 248 294 else lab side 250 304),F+r+n+3,
        phase X L n F r side v v c (min (j+1) r)⟩ := by
  let P := F+5*r+n+7; let E := F+r+n+3
  let T := phase X L n F r side v v c j
  have tf : Travel T L n Q F r := pTravel fr side v v c j
  have a := K (k := k) (P := P) (lab side 244 290) (lab side 245 291) E (E+1) T none .right
    (by cases side <;> decide) (by omega) (by omega) tf.d2 (by cases side <;> literal) rfl
  have b := sweepR (Cursor.q k (lab side 245 291)) T (E+1) j (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
    intro i lo hi
    have val : T i=some true := by
      change phase X L n F r side v v c j i=_
      rw [outDigit fr side v v c j i (by dsimp [E] at *; omega) (by dsimp [E] at *; omega),decide_eq_true (by dsimp [E] at *; omega)]
    rw [val]; cases side <;> literal)
  rw [show E+1+j=E+j+1 by omega] at b
  by_cases fits : j < r
  · let V := phase X L n F r side v v c (j+1)
    have val : T (E+j+1)=some false := by
      change phase X L n F r side v v c j (E+j+1)=_
      rw [outDigit fr side v v c j _ (by dsimp [E]; omega) (by dsimp [E]; omega),decide_eq_false (by dsimp [E]; omega)]
    have d := W (k := k) (P := P) (lab side 245 291) (lab side 246 292) (E+j+1) (E+j) T (some false) (some true) .left
      (by cases side <;> decide) (by omega) (by omega) val (by cases side <;> literal) (by simp [dest])
    have changeTape : put T (E+j+1) (some true)=V := advanceOut fr side v v c j fits
    rw [changeTape] at d
    have vf : Travel V L n Q F r := pTravel fr side v v c (j+1)
    have e := sweepL (Cursor.q k (lab side 246 292)) V E j (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
      intro i lo hi; obtain ⟨digit,hdigit⟩ := vf.b2 i (by dsimp [E] at *; omega) (by dsimp [E] at *; omega); rw [hdigit]; cases side <;> cases digit <;> literal)
    have f := K (k := k) (P := P) (lab side 246 292) (lab side 248 294) E E V none .stay
      (by cases side <;> decide) (by omega) (by omega) vf.d2 (by cases side <;> literal) rfl
    rw [if_pos fits,Nat.min_eq_left (by omega)]
    convert a.append b |>.append d |>.append e |>.append f using 1; omega
  · have full : j=r := by omega
    have val : T (E+j+1)=none := by rw [show E+j+1=F+2*r+n+4 by dsimp [E]; omega]; exact tf.d3
    have d := K (k := k) (P := P) (lab side 245 291) (lab side 247 293) (E+j+1) (E+j) T none .left
      (by cases side <;> decide) (by omega) (by omega) val (by cases side <;> literal) (by simp [dest])
    have e := sweepL (Cursor.q k (lab side 247 293)) T E j (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
      intro i lo hi; obtain ⟨digit,hdigit⟩ := tf.b2 i (by dsimp [E] at *; omega) (by dsimp [E] at *; omega); rw [hdigit]; cases side <;> cases digit <;> literal)
    have f := K (k := k) (P := P) (lab side 247 293) (lab side 250 304) E E T none .stay
      (by cases side <;> decide) (by omega) (by omega) tf.d2 (by cases side <;> literal) rfl
    have cap : min (j+1) r=j := by omega
    rw [if_neg fits,cap]
    convert a.append b |>.append d |>.append e |>.append f using 1; omega
private theorem fromCounter (k L n Q F r : Nat) (T : Nat → Option Bool) (fr : Travel T L n Q F r) (side : Bool) :
    ∃ t, t ≤ 16*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 248 294),F+r+n+3,T⟩ ⟨Cursor.q k (lab (!side) 209 254),sh (!side) L F r,T⟩ := by
  let P := F+5*r+n+7; have room := fr.room
  cases side
  · have a := CL k P 294 295 296 (F+r+2) n T (by omega) fr.d1 (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fr.d2)
      (by intro i lo hi; exact fr.b1 i lo (by omega)) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
    rw [show F+r+2+n+1=F+r+n+3 by omega] at a
    exact ⟨_,by omega,a.append (fromC_B k L n Q F r T fr)⟩
  · have a := CL k P 248 249 254 (F+r+2) n T (by omega) fr.d1 (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fr.d2)
      (by intro i lo hi; exact fr.b1 i lo (by omega)) (by literal) (by intro b; cases b <;> literal) (by literal) (by omega) (by omega)
    rw [show F+r+2+n+1=F+r+n+3 by omega] at a
    exact ⟨_,by omega,a⟩
private theorem cycle (k L n Q F r v j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (vp : 0 < v) (hv : v ≤ n) (hj : j ≤ r) (side : Bool) :
    ∃ t, t ≤ 256*(v+1)*(F+5*r+n+8) ∧
      if j < r then Path k (F+5*r+n+7) t
        ⟨Cursor.q k (lab side 209 254),sh side L F r,phase X L n F r side v 0 0 j⟩
        ⟨Cursor.q k (lab (!side) 209 254),sh (!side) L F r,phase X L n F r (!side) (v/2) 0 0 (j+1)⟩
      else Path k (F+5*r+n+7) t
        ⟨Cursor.q k (lab side 209 254),sh side L F r,phase X L n F r side v 0 0 j⟩
        ⟨Cursor.q k (lab side 250 304),F+r+n+3,phase X L n F r side v v (v/2) r⟩ := by
  obtain ⟨t,ht,a⟩ := halfToCounter k L n Q F r v j X fr vp hv side
  have b := increment k L n Q F r v (v/2) j X fr hj side
  by_cases fit : j < r
  · rw [if_pos fit,Nat.min_eq_left (by omega)] at b
    obtain ⟨u,hu,c⟩ := fromCounter k L n Q F r _ (pTravel fr side v v (v/2) (j+1)) side
    have path := a.append b |>.append c
    rw [turn] at path
    refine ⟨t+(2*j+3)+u,?_,by simpa only [if_pos fit] using path⟩
    have jm : j ≤ F+5*r+n+7 := by omega
    nlinarith only [ht,hu,jm,Nat.zero_le (v*(F+5*r+n+8))]
  · rw [if_neg fit,Nat.min_eq_right (by omega)] at b
    refine ⟨t+(2*j+3),?_,by simpa only [if_neg fit] using a.append b⟩
    have jm : j ≤ F+5*r+n+7 := by omega
    nlinarith only [ht,jm,Nat.zero_le (v*(F+5*r+n+8))]
private theorem empty (k L n Q F r j : Nat) (X : Nat → Option Bool)
    (fr : Frame X L n Q F r) (side : Bool) :
    ∃ t, t ≤ 32*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 209 254),sh side L F r,phase X L n F r side 0 0 0 j⟩
      ⟨Cursor.q k 308,L,phase X L n F r side 0 0 0 j⟩ := by
  let P := F+5*r+n+7; let S := sh side L F r
  let T := phase X L n F r side 0 0 0 j
  have room := fr.room
  have sf : S+n+1 ≤ P := by cases side <;> simp [S,sh,P] <;> omega
  have tf : Travel T L n Q F r := pTravel fr side 0 0 0 j
  have a := K (k := k) (P := P) (lab side 209 254) (lab side 210 255) S (S+1) T none .right
    (by cases side <;> decide) (by omega) (by omega) (srcNone tf side) (by cases side <;> literal) rfl
  have b := sweepR (Cursor.q k (lab side 210 255)) T (S+1) n (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
    intro i lo hi
    have val : T i=some false := by
      change phase X L n F r side 0 0 0 j i=_
      rw [srcDigit fr side 0 0 0 j i (by omega) (by omega),decide_eq_false (by omega)]
    rw [val]; cases side <;> literal)
  rw [show S+1+n=S+n+1 by omega] at b
  have c := K (k := k) (P := P) (lab side 210 255) (lab side 211 256) (S+n+1) (S+n) T none .left
    (by cases side <;> decide) (by omega) (by omega) (srcEnd tf side) (by cases side <;> literal) (by simp [dest])
  have d := sweepL (Cursor.q k (lab side 211 256)) T S n (good k _ (by cases side <;> decide)) (P := P) (by omega) (by
    intro i lo hi; obtain ⟨digit,hdigit⟩ := srcOcc tf side i lo (by omega); rw [hdigit]; cases side <;> cases digit <;> literal)
  have e := K (k := k) (P := P) (lab side 211 256) (lab side 212 257) S S T none .stay
    (by cases side <;> decide) (by omega) (by omega) (srcNone tf side) (by cases side <;> literal) rfl
  have tail : ∃ t, t ≤ 16*(P+1) ∧ Path k P t ⟨Cursor.q k (lab side 212 257),S,T⟩ ⟨Cursor.q k 308,L,T⟩ := by
    cases side
    · exact ⟨_,by dsimp [P]; omega,emptyB k L n Q F r T tf⟩
    · exact ⟨1,by omega,K (k := k) (P := P) 212 308 L L T none .stay (by omega) (by omega) (by omega) tf.sep (by literal) rfl⟩
  obtain ⟨u,hu,tail⟩ := tail
  exact ⟨_,by dsimp [P] at *; omega,a.append b |>.append c |>.append d |>.append e |>.append tail⟩
private theorem length_step (v : Nat) (hv : 0 < v) : bitLength v=bitLength (v/2)+1 := by
  by_cases two : 2 ≤ v
  · have hp : v/2 ≠ 0 := by omega
    simp only [bitLength,if_neg (by omega : v ≠ 0),if_neg hp]
    conv_lhs => rw [Nat.log2]
    rw [if_pos two]
  · have eq : v=1 := by omega
    subst v; simp [bitLength,Nat.log2]
private theorem quot_next (n j : Nat) : n/2^j/2=n/2^(j+1) := by
  rw [Nat.div_div_eq_div_mul,Nat.pow_succ]
private theorem parity_next (j : Nat) : (Bool.not (decide (j%2=0)))=decide ((j+1)%2=0) := by
  have h := Nat.mod_lt j (by decide : 0 < 2)
  have u := Nat.mod_lt (j+1) (by decide : 0 < 2)
  by_cases even : j%2=0
  · rw [decide_eq_true even,Bool.not_true,decide_eq_false (by omega)]
  · rw [decide_eq_false even,Bool.not_false,decide_eq_true (by omega)]
private theorem success_image {X L n Q F r} (fr : Frame X L n Q F r) (hg : bitLength n ≤ r) (side : Bool) :
    phase X L n F r side 0 0 0 (bitLength n)=RuntimeBitLength.Target.fullImage X L n F r := by
  have room := fr.room
  cases side <;> funext i <;>
    change img X L n F r 0 0 0 0 (bitLength n) i=RuntimeBitLength.Target.fullImage X L n F r i
  all_goals
    dsimp only [img,RuntimeBitLength.Target.fullImage]
    rw [Nat.min_eq_left hg]
    by_cases a : L < i ∧ i < L+n+1
    · rw [if_pos a,if_pos a,decide_eq_false (by omega),decide_eq_false (by omega)]
    · rw [if_neg a,if_neg a]
      by_cases b : F+r+2 < i ∧ i < F+r+n+3
      · rw [if_pos b,if_pos b,decide_eq_false (by omega),decide_eq_false (by omega)]
      · rw [if_neg b,if_neg b]
        by_cases c : F+r+n+3 < i ∧ i < F+2*r+n+4
        · rw [if_pos c]
          by_cases d : i ≤ F+r+n+3+bitLength n
          · rw [if_pos ⟨c.1,d⟩,decide_eq_true d]
          · rw [if_neg (by omega),decide_eq_false d,fr.b2 i c.1 c.2]
        · rw [if_neg c,if_neg (by omega)]
private theorem overflow_image {X L n Q F r} (fr : Frame X L n Q F r)
    (hg : r < bitLength n) (v : Nat) (eq : v/2=n/2^(r+1)) :
    phase X L n F r (decide (r%2=0)) v v (v/2) r=RuntimeBitLength.Target.fullImage X L n F r := by
  have room := fr.room
  funext i
  by_cases even : r%2=0
  · rw [decide_eq_true even]
    change img X L n F r v v 0 (v/2) r i=_
    have nextOdd : (r+1)%2=1 := by omega
    dsimp only [img,RuntimeBitLength.Target.fullImage]
    rw [Nat.min_eq_right (Nat.le_of_lt hg)]
    split_ifs <;> first | rfl | omega | (apply congrArg some; first | (apply decide_eq_decide.mpr; omega) | (apply decide_eq_true; omega))
  · rw [decide_eq_false even]
    change img X L n F r 0 (v/2) v v r i=_
    have nextEven : (r+1)%2=0 := by omega
    dsimp only [img,RuntimeBitLength.Target.fullImage]
    rw [Nat.min_eq_right (Nat.le_of_lt hg)]
    split_ifs <;> first | rfl | omega | (apply congrArg some; first | (apply decide_eq_decide.mpr; omega) | (apply decide_eq_true; omega))
private theorem overflow_label (r : Nat) :
    lab (decide (r%2=0)) 250 304=(if (r+1)%2=1 then 250 else 304) := by
  by_cases h : r%2=0
  · rw [decide_eq_true h,if_pos (by omega)]; rfl
  · rw [decide_eq_false h,if_neg (by omega)]; rfl
private def outcome (k L n F r : Nat) (X : Nat → Option Bool) : Node k :=
  ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
    if bitLength n ≤ r then L else F+r+n+3,RuntimeBitLength.Target.fullImage X L n F r⟩
private theorem loop (k L n Q F r : Nat) (X : Nat → Option Bool) (fr : Frame X L n Q F r)
    (v j : Nat) (side : Bool) (hv : v ≤ n) (hj : j ≤ r)
    (value : v=n/2^j) (sum : j+bitLength v=bitLength n) (parity : side=decide (j%2=0)) :
    ∃ t, t ≤ 1024*(v+1)*(F+5*r+n+8) ∧ Path k (F+5*r+n+7) t
      ⟨Cursor.q k (lab side 209 254),sh side L F r,phase X L n F r side v 0 0 j⟩ (outcome k L n F r X) := by
  induction v using Nat.strong_induction_on generalizing j side with
  | h v ih =>
    by_cases zero : v=0
    · have gj : bitLength n=j := by
        have h : bitLength 0=0 := rfl
        rw [zero,h,Nat.add_zero] at sum
        exact sum.symm
      have fits : bitLength n ≤ r := by omega
      obtain ⟨t,ht,path⟩ := empty k L n Q F r j X fr side
      have image : phase X L n F r side 0 0 0 j=RuntimeBitLength.Target.fullImage X L n F r := by rw [← gj]; exact success_image fr fits side
      have final : (⟨Cursor.q k 308,L,phase X L n F r side 0 0 0 j⟩ : Node k)=outcome k L n F r X := by simp only [outcome,if_pos fits,image]
      rw [final] at path
      refine ⟨t,?_,by simpa only [zero] using path⟩
      simpa only [zero,Nat.zero_add,Nat.mul_one] using (ht.trans (show 32*(F+5*r+n+8) ≤ 1024*(F+5*r+n+8) by omega))
    · have vp : 0 < v := by omega
      obtain ⟨t,ht,path⟩ := cycle k L n Q F r v j X fr vp hv hj side
      by_cases fit : j < r
      · rw [if_pos fit] at path
        have value' : v/2=n/2^(j+1) := by rw [value,quot_next]
        have sum' : j+1+bitLength (v/2)=bitLength n := by have h := length_step v vp; omega
        have parity' : (Bool.not side)=decide ((j+1)%2=0) := by rw [parity,parity_next]
        obtain ⟨u,hu,rest⟩ := ih (v/2) (by omega) (j+1) (!side) (by omega) (by omega) value' sum' parity'
        have twice := Nat.mul_le_mul_right (512*(F+5*r+n+8)) (show 2*(v/2) ≤ v by omega)
        have positive := Nat.mul_le_mul_right (256*(F+5*r+n+8)) (show 1 ≤ v by omega)
        exact ⟨t+u,by nlinarith only [ht,hu,twice,positive,Nat.zero_le (v*(F+5*r+n+8))],path.append rest⟩
      · rw [if_neg fit] at path
        have jr : j=r := by omega
        subst j
        have positive : 0 < bitLength v := by have h := length_step v vp; omega
        have overflow : r < bitLength n := by omega
        have quotient : v/2=n/2^(r+1) := by rw [value,quot_next]
        have final : (⟨Cursor.q k (lab side 250 304),F+r+n+3,phase X L n F r side v v (v/2) r⟩ : Node k)=outcome k L n F r X := by
          rw [parity,overflow_image fr overflow v quotient,overflow_label]
          simp only [outcome,if_neg (by omega : ¬bitLength n ≤ r)]
        rw [final] at path
        exact ⟨t,by nlinarith only [ht,Nat.zero_le ((v+1)*(F+5*r+n+8))],path⟩
elab "fromH " key:str " => " tac:tacticSeq : tactic => do
  let names := [← PartAPrivateControl.selectText "RuntimeBitLength.Kernel" "RuntimeBitLength" key.getString]
  unless names.length=1 do throwError "Ambiguous immutable H application: {names}"
  logInfo m!"private-term|{names.head!}"
  evalTactic (tac.raw.rewriteBottomUp fun stx =>
    if stx.isIdent && stx.getId.toString=="OLD" then mkIdent names.head! else stx)
private theorem next_constraint (k d : Nat)
    (h : (Cursor.q k d).val < 250 ∨ (Cursor.q k d).val=254) :
    d < 250 ∨ d=254 ∨ Cursor.stateCount k ≤ d := by
  by_cases bound : d < Cursor.stateCount k
  · have eq : (Cursor.q k d).val=d := Nat.mod_eq_of_lt bound
    rw [eq] at h
    omega
  · omega
private theorem early_bound {k N B t : Nat} (C : Config (Cursor.machine k).stateCount N B)
    (last : ((Cursor.machine k).run t C).state.val < 250 ∨ ((Cursor.machine k).run t C).state.val=254)
    (before : ∀ u, u < t → ((Cursor.machine k).run u C).state.val < 254) :
    ∀ u, u < t → ((Cursor.machine k).run u C).state.val < 250 := by
  have backward (D : Config (Cursor.machine k).stateCount N B) (hd : D.state.val < 254)
      (next : ((Cursor.machine k).stepConfig D).state.val < 250 ∨ ((Cursor.machine k).stepConfig D).state.val=254) : D.state.val < 250 := by
    by_contra bad
    have cases4 : D.state.val=250 ∨ D.state.val=251 ∨ D.state.val=252 ∨ D.state.val=253 := by omega
    have state : D.state=Cursor.q k D.state.val := by apply Fin.ext; exact (Nat.mod_eq_of_lt D.state.isLt).symm
    change (((Cursor.machine k).step D.state (D.tape D.head)).1).val < 250 ∨ (((Cursor.machine k).step D.state (D.tape D.head)).1).val=254 at next
    rw [state] at next
    rcases cases4 with h|h|h|h
    all_goals
      cases value : D.tape D.head with
      | none =>
        rw [value] at next
        have row := row_value k D.state.val none (by omega) (by omega)
        rw [h] at row next
        delta instructions at row
        simp at row
        rw [row] at next
        have impossible := next_constraint k _ next
        unfold Cursor.stateCount at impossible
        omega
      | some b =>
        rw [value] at next
        cases b
        all_goals first
        | (have row := row_value k D.state.val (some false) (by omega) (by omega)
           rw [h] at row next
           delta instructions at row
           simp at row
           rw [row] at next
           have impossible := next_constraint k _ next
           unfold Cursor.stateCount at impossible
           omega)
        | (have row := row_value k D.state.val (some true) (by omega) (by omega)
           rw [h] at row next
           delta instructions at row
           simp at row
           rw [row] at next
           have impossible := next_constraint k _ next
           unfold Cursor.stateCount at impossible
           omega)
  have aux : ∀ d u, u+d=t → ((Cursor.machine k).run u C).state.val < 250 ∨ ((Cursor.machine k).run u C).state.val=254 := by
    intro d
    induction d with
    | zero =>
      intro u eq
      have e : u=t := by omega
      simpa only [e] using last
    | succ d ih =>
      intro u eq
      have h := ih (u+1) (by omega)
      have next : (Cursor.machine k).run (u+1) C=(Cursor.machine k).stepConfig ((Cursor.machine k).run u C) := by rw [show u+1=u+1 from rfl,UniformTM.run_add]; rfl
      rw [next] at h
      exact Or.inl (backward _ (before u (by omega)) h)
  intro u hu
  have h := aux (t-u) u (by omega)
  have ub := before u hu
  omega
private theorem initial_image {X L n Q F r} (fr : Frame X L n Q F r) : phase X L n F r true n 0 0 0=X := by
  funext i
  change img X L n F r 0 n 0 0 0 i=X i
  simp only [img]
  split_ifs <;> first | rfl | (rw [fr.assn i (by omega) (by omega),decide_eq_true (by omega)]) | (rw [fr.b1 i (by omega) (by omega),decide_eq_false (by omega)]) | (rw [fr.b2 i (by omega) (by omega),decide_eq_false (by omega)])
private theorem first_image {X L n Q F r} (fr : Frame X L n Q F r) (hr : 0 < r) :
    RuntimeBitLength.Target.image X L n F r=phase X L n F r false (n/2) 0 0 1 := by
  have room := fr.room
  funext i
  change RuntimeBitLength.Target.image X L n F r i=img X L n F r 0 0 0 (n/2) 1 i
  dsimp only [RuntimeBitLength.Target.image,img]
  split_ifs <;> first | rfl | omega | (rw [fr.b1 i (by omega) (by omega),decide_eq_false (by omega)]) | (rw [fr.b2 i (by omega) (by omega),decide_eq_false (by omega)]) | (symm; apply congrArg some; first | (apply decide_eq_true; omega) | (apply decide_eq_false; omega))
theorem prepared (k N B L n Q F r : Nat) (X : Nat → Option Bool) : Prepared k N B L n Q F r X := by
  intro hn hr paid room sep assn right marks gap fence d0 b0 d1 b1 d2 b2 d3 fit
  have fr : Frame X L n Q F r := ⟨paid,room,sep,assn,right,marks,gap,fence,d0,b0,d1,b1,d2,b2,d3⟩
  let C : Config (Cursor.machine k).stateCount N B := ⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩
  have segment : ∃ (a j v : Nat) (side : Bool), a ≤ 128*(n+1)*(F+5*r+n+8) ∧
      j ≤ r ∧ v ≤ n ∧ v=n/2^j ∧ j+bitLength v=bitLength n ∧ side=decide (j%2=0) ∧
      (∀ u, u < a → ((Cursor.machine k).run u C).state.val < 250) ∧
      (Cursor.machine k).run a C=embed (N := N) (B := B)
        ⟨Cursor.q k (lab side 209 254),sh side L F r,phase X L n F r side v 0 0 j⟩ (by cases side <;> simp only [sh,Bool.false_eq_true,ite_false,ite_true] <;> omega) := by
    by_cases two : 2 ≤ n
    · obtain ⟨a,ha,run,before⟩ := RuntimeBitLength.halve k N B L n Q F r X two hr paid room sep assn right marks gap fence d0 b0 d1 b1 d2 (b2 _ (by omega) (by omega)) fit
      refine ⟨a,1,n/2,false,ha,by omega,by omega,by simp,?_,rfl,?_,?_⟩
      · have h := length_step n hn; omega
      · apply early_bound C (Or.inr ?_) before
        rw [run]; rfl
      · rw [run,first_image fr hr]; rfl
    · have entry : ∃ a, a ≤ 16*(F+5*r+n+8) ∧ (Cursor.machine k).run a C=
          (⟨Cursor.q k 209,⟨L,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B) ∧
          (∀ u, u < a → ((Cursor.machine k).run u C).state.val < 254) := by
        fromH "Frame.mk" => have oldframe := OLD paid room sep assn right marks gap fence d0 b0 d1 b1 d2 (b2 _ (by omega) (by omega))
        fromH "entry" => obtain ⟨a,_,ha,path⟩ := OLD k L n Q F r X oldframe
        refine ⟨a,ha,?_,?_⟩
        · fromH "Path.execute" => exact OLD path fit
        · fromH "Path.first" => exact OLD path fit
      obtain ⟨a,ha,run,before⟩ := entry
      refine ⟨a,0,n,true,by nlinarith only [ha,Nat.zero_le (n*(F+5*r+n+8))],by omega,le_rfl,by simp,by simp,rfl,?_,?_⟩
      · apply early_bound C (Or.inl ?_) before
        rw [run]; change 209 < 250; omega
      · rw [run,initial_image fr]; rfl
  obtain ⟨a,j,v,side,ha,hj,hv,value,sum,parity,before,run⟩ := segment
  obtain ⟨b,hb,path⟩ := loop k L n Q F r X fr v j side hv hj value sum parity
  have ex := path.execute fit
  have price := Nat.mul_le_mul_right (1024*(F+5*r+n+8)) (show v+1 ≤ n+1 by omega)
  have len : n+1 ≤ (n+r+1)^2 := by nlinarith only [Nat.zero_le n,Nat.zero_le r,Nat.zero_le (n^2),Nat.zero_le (r^2)]
  have slack := Nat.mul_le_mul_right (4096*(F+5*r+n+8)) len
  have total : a+b ≤ 4096*(n+r+1)^2*(F+5*r+n+8) := by nlinarith only [ha,hb,price,slack,Nat.zero_le ((n+1)*(F+5*r+n+8))]
  have headFit : (if bitLength n ≤ r then L else F+r+n+3) < tapeLength N B := by split <;> omega
  refine ⟨a+b,headFit,total,?_,?_⟩
  · intro u hu s hs
    by_cases h : u<a
    · have bound := before u h
      have smem : s=308 ∨ s=250 ∨ s=304 := by simpa using hs
      intro eq
      have bad : 250 ≤ ((Cursor.machine k).run u C).state.val := by
        rw [eq]
        change 250 ≤ s % Cursor.stateCount k
        rw [small_mod k s (by omega)]
        omega
      omega
    · have shift : u=a+(u-a) := by omega
      rw [shift,UniformTM.run_add,run]
      have guard := path.first fit (u-a) (by omega)
      intro eq
      have smem : s=308 ∨ s=250 ∨ s=304 := by simpa using hs
      have sv : (Cursor.q k s).val=s := small_mod k s (by omega)
      have equal := (congrArg Fin.val eq).trans sv
      rcases smem with h308|h250|h304
      · exact guard.2.2 (equal.trans h308)
      · exact guard.1 (equal.trans h250)
      · exact guard.2.1 (equal.trans h304)
  · rw [UniformTM.run_add,run,ex]; rfl
end BitLengthDriver
