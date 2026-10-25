import CappedWeight.Rows
namespace CappedWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 10000
private structure Node (k : Nat) where
  state : Fin (Cursor.stateCount k)
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {k N B : Nat} (c : Node k) (h : c.head  <  tapeLength N B) : Config (Cursor.stateCount k) N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (k P : Nat) (c d : Node k) : Prop where
  safe : c.state.val  <  411
  before : c.head      ≤      P
  after : d.head      ≤      P
  row : ((Cursor.machine k).step c.state (c.tape c.head)).1 = d.state
  move : dest c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.1
private inductive Path (k P : Nat) : Nat → Node k → Node k → Prop
  | nil (c) (h : c.head      ≤      P) : Path k P 0 c c
  | cons {t c d e} : Edge k P c d → Path k P t d e → Path k P (t+1) c e
namespace Path
private theorem bounds {k P t c d} (h : Path k P t c d) : c.head      ≤      P ∧ d.head      ≤      P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {k P t u c d e} (h : Path k P t c d) (g : Path k P u d e) :
    Path k P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {k N B P t c d} (h : Path k P t c d) (hp : P  <  tapeLength N B) :
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
        have hr : c.head+1  <  tapeLength N B := by omega
        simp only [moveHead,embed,hr,↓reduceDIte]
        exact hm
    · funext i
      dsimp only [UniformTM.stepConfig,embed]
      rw [e.tape]
      simp only [put,Fin.ext_iff]
  suffices aux : ∀ (hc : c.head  <  tapeLength N B) (hd : d.head  <  tapeLength N B),
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
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hs : s.val  <  411) (hb : h      ≤      P) (ha : h'      ≤      P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hs,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hs : s.val  <  411) (hb : h      ≤      P) (ha : h'      ≤      P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hs hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (hs : s.val  <  411) (fit : h+r      ≤      P) (rows : ∀ i, h      ≤      i → i  <  h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right hs (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (hs : s.val  <  411) (fit : low+r      ≤      P) (rows : ∀ i, low  <  i → i      ≤      low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left hs (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private theorem Path.first {k N B P t c d} (path : Path k P t c d) (hp : P  <  tapeLength N B)
    (u : Nat) (hu : u  <  t) :
    ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val  <  411 := by
  induction path generalizing u with
  | nil => omega
  | @cons t c d e edge rest ih =>
    cases u with
    | zero => exact edge.safe
    | succ u =>
      have one : Path k P 1 c d := Path.cons edge (Path.nil d edge.after)
      rw [show u+1=1+u by omega,UniformTM.run_add,one.execute hp]
      exact ih u (by omega)
private theorem small_mod (k i : Nat) (h : i    ≤    798+93*k) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private def rowTac : TacticM Unit := withMainContext do
  let goal ← getMainGoal; let target ← Lean.Meta.whnf (← instantiateMVars (← goal.getType))
  unless target.isAppOfArity ``Eq 3 do throwError "power row equality expected"
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
  let kv ← PrettyPrinter.delab stateArgs[0]!
  let sv ← PrettyPrinter.delab src; let cv ← PrettyPrinter.delab code
  let bv ← PrettyPrinter.delab args[2]!; let dv ← PrettyPrinter.delab dst
  let tagv:=quote tag; let movev:=quote move; let offsetv:=quote (3*tag+move)
  evalTactic (← `(tactic| (
    have checkedRow := CappedWeight.phase_row $kv:term $sv:term $cv:term $bv:term (by omega) (by omega) (by omega) (by first | rfl | (norm_num [instructions] <;> omega))
    have destEq : $cv:term / 9=$dv:term := by first | rfl | (change (9*$dv:term+$offsetv:term)/9=$dv:term; omega)
    have symbolEq : $cv:term / 3 % 3=$tagv:term := by first | rfl | (change (9*$dv:term+$offsetv:term)/3%3=$tagv:term; omega)
    have moveEq : $cv:term % 3=$movev:term := by first | rfl | (change (9*$dv:term+$offsetv:term)%3=$movev:term; omega)
    simpa only [destEq,symbolEq,moveEq] using checkedRow)))
private theorem K {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (mv : Move)
    (safe : s  <  411) (hb : h    ≤    P) (ha : h'    ≤    P) (value : T h=b)
    (row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k d,b,mv)) (hm : dest h mv=h') :
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ := by
  apply keep _ _ _ _ _ _ ?_ hb ha (by rw [value]; exact row) hm
  simpa only [Cursor.q,small_mod k s (by omega)] using safe
private theorem crossR {k P : Nat} (s scan out low width : Nat) (T : Nat → Option Bool)
    (hs : s < 411) (hscan : scan < 411) (fit : low+width+1   ≤   P)
    (d : T low=none) (endD : T (low+width+1)=none)
    (occ : ∀ i, low < i → i < low+width+1 → ∃ b, T i=some b)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k scan,none,.right))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k scan) (some b)=(Cursor.q k scan,some b,.right))
    (exit : (Cursor.machine k).step (Cursor.q k scan) none=(Cursor.q k out,none,.stay)) :
    Path k P (width+2) ⟨Cursor.q k s,low,T⟩ ⟨Cursor.q k out,low+width+1,T⟩ := by
  have a := K (k:=k) s scan low (low+1) T none .right hs (P:=P) (by omega) (by omega) d entry rfl
  have b := sweepR (Cursor.q k scan) T (low+1) width
    (by change scan % Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; exact hscan) (P:=P) (by omega) (by
      intro i lo hi; obtain ⟨b,hb⟩ := occ i (by omega) (by omega); rw [hb]; exact body b)
  rw [show low+1+width=low+width+1 by omega] at b
  have c := K (k:=k) scan out (low+width+1) (low+width+1) T none .stay hscan (P:=P) (by omega) (by omega) endD exit rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b |>.append c
private theorem crossL {k P : Nat} (s scan out low width : Nat) (T : Nat → Option Bool)
    (hs : s < 411) (hscan : scan < 411) (fit : low+width+1   ≤   P)
    (d : T low=none) (endD : T (low+width+1)=none)
    (occ : ∀ i, low < i → i < low+width+1 → ∃ b, T i=some b)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k scan,none,.left))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k scan) (some b)=(Cursor.q k scan,some b,.left))
    (exit : (Cursor.machine k).step (Cursor.q k scan) none=(Cursor.q k out,none,.stay)) :
    Path k P (width+2) ⟨Cursor.q k s,low+width+1,T⟩ ⟨Cursor.q k out,low,T⟩ := by
  have a := K (k:=k) s scan (low+width+1) (low+width) T none .left hs (P:=P) (by omega) (by omega) endD entry (by simp [dest])
  have b := sweepL (Cursor.q k scan) T low width
    (by change scan % Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; exact hscan) (P:=P) (by omega) (by
      intro i lo hi; obtain ⟨b,hb⟩ := occ i lo (by omega); rw [hb]; exact body b)
  have c := K (k:=k) scan out low low T none .stay hscan (P:=P) (by omega) (by omega) d exit rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b |>.append c
private def D (F r n j : Nat) : Nat := match j with
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def width (n r j : Nat) : Nat := if j=1 then n else r
private structure Frame (T : Nat → Option Bool) (L n Q F r : Nat) : Prop where
  paid : 0 < Q
  room : L+n+1+Q < F
  sep : T L=none
  right : T (L+n+1)=none
  marks : ∀ i, L+n+1 < i → i   ≤   L+n+1+Q → T i=some true
  gap : ∀ i, L+n+1+Q < i → i < F → T i=none
  fence : T F=some false
  ds : ∀ j, j   ≤   6 → T (D F r n j)=none
  banks : ∀ j, j < 6 → ∀ i, D F r n j < i → i < D F r n (j+1) →
    T i=some (decide (i   ≤   D F r n j+(if j=0 then r else if j=2 then Pnp4.Frontier.ContractExpansion.bitLength n else if j=3 then 1 else 0)))
  assn : ∀ i, L < i → i < L+n+1 → T i=some false
private def I (T : Nat → Option Bool) (L n F r a b d : Nat) : Nat → Option Bool :=
  Target.image T L n F r (Pnp4.Frontier.ContractExpansion.bitLength n) a b 0 d
private theorem old {T L n Q F r} (_fr : Frame T L n Q F r) (a b d i : Nat)
    (hA : i   ≤   L ∨ L+n+1   ≤   i) (hB : i   ≤   F+r+n+3 ∨ F+5*r+n+7   ≤   i ∨
      i=F+2*r+n+4 ∨ i=F+3*r+n+5 ∨ i=F+4*r+n+6) : I T L n F r a b d i=T i := by
  dsimp only [I,Target.image]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
private theorem atD {T L n Q F r} (fr : Frame T L n Q F r) (a b d j : Nat) (hj : j   ≤   6) :
    I T L n F r a b d (D F r n j)=none := by
  rw [old fr a b d _ (by have h := fr.room; interval_cases j <;> dsimp [D] <;> omega)
    (by interval_cases j <;> dsimp [D] <;> omega)]
  exact fr.ds j hj
private theorem bank {T L n Q F r} (fr : Frame T L n Q F r) (a b d j : Nat) (hj : j < 6) :
    ∀ i, D F r n j < i → i < D F r n (j+1) → ∃ bit, I T L n F r a b d i=some bit := by
  intro i lo hi
  have room:=fr.room
  interval_cases j
  case «0» =>
    exact ⟨_,(old fr a b d i (by dsimp [D] at lo hi; omega) (by dsimp [D] at lo hi; omega)).trans (fr.banks 0 (by omega) i lo hi)⟩
  case «1» =>
    exact ⟨_,(old fr a b d i (by dsimp [D] at lo hi; omega) (by dsimp [D] at lo hi; omega)).trans (fr.banks 1 (by omega) i lo hi)⟩
  all_goals
    dsimp [D] at lo hi
    dsimp only [I,Target.image]
    split_ifs <;> first | exact ⟨_,rfl⟩ | omega
private theorem initial_image {T L n Q F r} (fr : Frame T L n Q F r) : I T L n F r 1 0 0=T := by
  funext i
  dsimp only [I,Target.image]
  split_ifs with a b c d e
  · rw [fr.assn i a.1 a.2]; congr 1; simp only [Nat.sub_zero]; exact decide_eq_false (by omega)
  · exact (fr.banks 2 (by omega) i b.1 b.2).symm
  · exact (fr.banks 3 (by omega) i c.1 c.2).symm
  · rw [fr.banks 4 (by omega) i d.1 d.2]; rfl
  · rw [fr.banks 5 (by omega) i e.1 e.2]; rfl
  · rfl
private theorem set3 {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) (ha : a < r) :
    put (I T L n F r a b d) (D F r n 3+a+1) (some true)=I T L n F r (a+1) b d := by
  funext i
  dsimp only [put,I,Target.image,D]
  have h := fr.room
  by_cases cell : i=F+2*r+n+4+a+1
  · subst i; split_ifs <;> simp_all <;> omega
  · rw [if_neg cell]
    have eq : (i   ≤   F+2*r+n+4+a) ↔ i   ≤   F+2*r+n+4+(a+1) := by omega
    simp only [eq]
private theorem set4 {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) (hb : b < r) :
    put (I T L n F r a b d) (D F r n 4+b+1) (some true)=I T L n F r a (b+1) d := by
  funext i
  dsimp only [put,I,Target.image,D]
  have h := fr.room
  by_cases cell : i=F+3*r+n+5+b+1
  · subst i; split_ifs <;> simp_all <;> omega
  · rw [if_neg cell]
    have eq : (i   ≤   F+3*r+n+5+b) ↔ i   ≤   F+3*r+n+5+(b+1) := by omega
    simp only [eq]
private theorem unset3 {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) (ha : a < r) :
    put (I T L n F r (a+1) b d) (D F r n 3+a+1) (some false)=I T L n F r a b d := by
  funext i; dsimp only [put,I,Target.image,D]; have h:=fr.room
  by_cases cell : i=F+2*r+n+4+a+1
  · subst i; split_ifs <;> simp_all <;> omega
  · rw [if_neg cell]
    have eq : (i   ≤   F+2*r+n+4+a) ↔ i   ≤   F+2*r+n+4+(a+1) := by omega
    simp only [eq]
private theorem unset4 {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) (hb : b < r) :
    put (I T L n F r a (b+1) d) (D F r n 4+b+1) (some false)=I T L n F r a b d := by
  funext i; dsimp only [put,I,Target.image,D]; have h:=fr.room
  by_cases cell : i=F+3*r+n+5+b+1
  · subst i; split_ifs <;> simp_all <;> omega
  · rw [if_neg cell]
    have eq : (i   ≤   F+3*r+n+5+b) ↔ i   ≤   F+3*r+n+5+(b+1) := by omega
    simp only [eq]
private theorem mark {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) (hd : d < n) :
    put (I T L n F r a b d) (L+n-d) (some true)=I T L n F r a b (d+1) := by
  funext i; dsimp only [put,I,Target.image]; have h:=fr.room
  by_cases cell : i=L+n-d
  · subst i; split_ifs <;> simp_all <;> omega
  · rw [if_neg cell]
    have eq : (L+n+1-d   ≤   i) ↔ L+n+1-(d+1)   ≤   i := by omega
    simp only [eq]
private theorem unmark {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) (hd : d < n) :
    put (I T L n F r a b (d+1)) (L+n-d) (some false)=I T L n F r a b d := by
  funext i; dsimp only [put,I,Target.image]; have h:=fr.room
  by_cases cell : i=L+n-d
  · subst i; split_ifs <;> simp_all <;> omega
  · rw [if_neg cell]
    have eq : (L+n+1-d   ≤   i) ↔ L+n+1-(d+1)   ≤   i := by omega
    simp only [eq]
private theorem inc {k P : Nat} (s yes no base w v : Nat) (T : Nat → Option Bool)
    (safe : s+3 < 411) (fit : base+w+1   ≤   P) (hv : v   ≤   w) (sep : T base=none) (endD : T (base+w+1)=none)
    (unary : ∀ i, base < i → i < base+w+1 → T i=some (decide (i   ≤   base+v)))
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right))
    (add : (Cursor.machine k).step (Cursor.q k (s+1)) (some false)=(Cursor.q k (s+2),some true,.left))
    (full : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+3),none,.left))
    (back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+2)) (some b)=(Cursor.q k (s+2),some b,.left))
    (ok : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k yes,none,.stay))
    (bad : (Cursor.machine k).step (Cursor.q k (s+3)) (some true)=(Cursor.q k (s+3),some true,.left))
    (over : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k no,none,.stay)) :
    Path k P (2*v+3) ⟨Cursor.q k s,base,T⟩
      ⟨Cursor.q k (if v < w then yes else no),base,if v < w then put T (base+v+1) (some true) else T⟩ := by
  have first := K (k:=k) s (s+1) base (base+1) T none .right (by omega) (P:=P) (by omega) (by omega) sep entry rfl
  have fwd := sweepR (Cursor.q k (s+1)) T (base+1) v
    (by change (s+1)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
      intro i lo hi; have val:=unary i (by omega) (by omega)
      rw [show T i=some true by simpa only [decide_eq_true (by omega : i   ≤   base+v)] using val]; exact scan)
  rw [show base+1+v=base+v+1 by omega] at fwd
  by_cases fits : v < w
  · have val : T (base+v+1)=some false := by
      have u:=unary (base+v+1) (by omega) (by omega); simpa only [decide_eq_false (by omega : ¬base+v+1   ≤   base+v)] using u
    have changeTape := hop (P:=P) (Cursor.q k (s+1)) (Cursor.q k (s+2)) (base+v+1) (base+v) T (some true) .left
      (by change (s+1)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (by omega) (by omega) (by rw [val]; exact add) (by simp [dest])
    let U:=put T (base+v+1) (some true)
    have rev:=sweepL (Cursor.q k (s+2)) U base v
      (by change (s+2)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
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
      (by change (s+3)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
        intro i lo hi; have u:=unary i lo (by omega); rw [u,decide_eq_true hi]; exact bad)
    have last:=K (k:=k) (s+3) no base base T none .stay (by omega) (P:=P) (by omega) (by omega) sep over rfl
    simpa only [if_neg fits,show 1+v+1+v+1=2*v+3 by omega] using first.append fwd |>.append turn |>.append rev |>.append last
private theorem dec {k P : Nat} (s yes no base w v : Nat) (T : Nat → Option Bool)
    (safe : s+3 < 411) (fit : base+w+1  ≤  P) (hv : v  ≤  w) (sep : T base=none) (endD : T (base+w+1)=none)
    (unary : ∀ i, base < i → i < base+w+1 → T i=some (decide (i  ≤  base+v)))
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right))
    (tail : ∀ b, b≠some true → (Cursor.machine k).step (Cursor.q k (s+1)) b=(Cursor.q k (s+2),b,.left))
    (take : (Cursor.machine k).step (Cursor.q k (s+2)) (some true)=(Cursor.q k (s+3),some false,.left))
    (back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+3)) (some b)=(Cursor.q k (s+3),some b,.left))
    (ok : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k yes,none,.stay))
    (empty : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k no,none,.stay)) :
    Path k P (2*v+3) ⟨Cursor.q k s,base,T⟩
      ⟨Cursor.q k (if v=0 then no else yes),base,if v=0 then T else put T (base+v) (some false)⟩ := by
  have first:=K (k:=k) s (s+1) base (base+1) T none .right (by omega) (P:=P) (by omega) (by omega) sep entry rfl
  have fwd:=sweepR (Cursor.q k (s+1)) T (base+1) v
    (by change (s+1)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
      intro i lo hi; have u:=unary i (by omega) (by omega)
      rw [u,decide_eq_true (by omega : i  ≤  base+v)]; exact scan)
  rw [show base+1+v=base+v+1 by omega] at fwd
  have next : T (base+v+1)≠some true := by
    by_cases full : v=w
    · rw [full,endD]; decide
    · have u:=unary (base+v+1) (by omega) (by omega)
      rw [u,decide_eq_false (by omega : ¬base+v+1  ≤  base+v)]; decide
  have turn:=keep (Cursor.q k (s+1)) (Cursor.q k (s+2)) (base+v+1) (base+v) T .left
    (by change (s+1)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by omega) (tail _ next) (by simp [dest])
  by_cases zero : v=0
  · subst v
    have last:=K (k:=k) (s+2) no base base T none .stay (by omega) (P:=P) (by omega) (by omega) sep empty rfl
    simpa using first.append fwd |>.append turn |>.append last
  · obtain ⟨a,rfl⟩ : ∃ a, v=a+1 := ⟨v-1,by omega⟩
    have cell : T (base+(a+1))=some true := by
      rw [unary _ (by omega) (by omega),decide_eq_true (by omega)]
    have write:=hop (P:=P) (Cursor.q k (s+2)) (Cursor.q k (s+3)) (base+(a+1)) (base+a) T (some false) .left
      (by change (s+2)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (by omega) (by omega) (by rw [cell]; exact take) (by simp [dest])
    let U:=put T (base+(a+1)) (some false)
    have rev:=sweepL (Cursor.q k (s+3)) U base a
      (by change (s+3)%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by omega) (by
        intro i lo hi
        have eq : U i=T i := by dsimp [U,put]; rw [if_neg (by omega)]
        rw [eq,unary _ lo (by omega)]; exact back _)
    have last:=K (k:=k) (s+3) yes base base U none .stay (by omega) (P:=P) (by omega) (by omega)
      (by dsimp [U,put]; rw [if_neg (by omega)]; exact sep) ok rfl
    simpa only [if_neg (by omega : a+1≠0),show 1+(a+1)+1+1+a+1=2*(a+1)+3 by omega] using
      first.append fwd |>.append turn |>.append write |>.append rev |>.append last
private def travelTac (ss : Nat) (out : String) (fromBank toBank : Nat) : TacticM Unit := do
  unless fromBank≠toBank do throwError "travel expects a nonempty fixed bank route"
  let right := fromBank < toBank; let count:=if right then toBank-fromBank else fromBank-toBank
  let mut text:=""
  for z in List.range count do
    let j:=if right then fromBank+z else fromBank-z-1
    let dest:=if z+1=count then out else toString (ss+2*(z+1))
    let r:=toString j; let next:=toString (j+1); let v:=toString z
    text:=text++s!"have he{v} : D F r n {r}+width n r {r}+1=D F r n {next} := by dsimp [D,width]; omega\n"
    text:=text++s!"have tr{v} := cross{if right then "R" else "L"} (k:=k) (P:=P) {ss+2*z} {ss+2*z+1} ({dest}) (D F r n {r}) (width n r {r}) (I T L n F r a b d) (by omega) (by omega) (by dsimp [D,width,P]; omega) (atD fr a b d {j} (by omega)) (by rw [he{v}]; exact atD fr a b d {j+1} (by omega)) (by intro i lo hi; exact bank fr a b d {j} (by omega) i lo (by rw [← he{v}]; exact hi)) (by run_tac rowTac) (by intro bit; cases bit <;> run_tac rowTac) (by run_tac rowTac)\n"
    text:=text++s!"rw [he{v}] at tr{v}\n"
  let parts := (List.range count).map fun j => "tr"++toString j
  text:=text++"have path := "++String.intercalate " |>.append " parts++"\nrefine ⟨_,?_,path⟩\ndsimp only [P,width,D]\nsplit_ifs <;> omega"
  let ast ← ofExcept (Parser.runParserCategory (← getEnv) `tactic ("(\n  "++text.replace "\n" "\n  "++"\n)"))
  evalTactic ast
private theorem unary3 {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) :
    ∀ i, D F r n 3 < i → i < D F r n 4 → I T L n F r a b d i=some (decide (i ≤ D F r n 3+a)) := by
  intro i lo hi; dsimp only [D] at lo hi ⊢; dsimp only [I,Target.image]
  have h:=fr.room
  rw [if_neg (by omega),if_neg (by omega),if_pos ⟨lo,hi⟩]
private theorem unary4 {T L n Q F r} (fr : Frame T L n Q F r) (a b d : Nat) :
    ∀ i, D F r n 4 < i → i < D F r n 5 → I T L n F r a b d i=some (decide (i ≤ D F r n 4+b)) := by
  intro i lo hi; dsimp only [D] at lo hi ⊢; dsimp only [I,Target.image]
  have h:=fr.room
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos ⟨lo,hi⟩]
private theorem assignment {T L n Q F r} (_fr : Frame T L n Q F r) (a b d i : Nat)
    (lo : L < i) (hi : i < L+n+1) : I T L n F r a b d i=some (decide (L+n+1-d ≤ i)) := by
  dsimp only [I,Target.image]; rw [if_pos ⟨lo,hi⟩]
private theorem backH {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (a b d : Nat) (mode : Bool) :
    let P:=F+5*r+n+7
    ∃ t, t ≤ 16*(P+1) ∧ Path k P t
      ⟨Cursor.q k (if mode then 333 else 360),D F r n (if mode then 3 else 4),I T L n F r a b d⟩
      ⟨Cursor.q k 343,L+n+1,I T L n F r a b d⟩ := by
  dsimp only
  let P:=F+5*r+n+7
  let J:=I T L n F r a b d
  have Hnone : J (L+n+1)=none := (old fr a b d _ (by omega) (by have h:=fr.room; omega)).trans fr.right
  have Ffalse : J F=some false := (old fr a b d _ (by have h:=fr.room; omega) (by omega)).trans fr.fence
  have blank (i : Nat) (lo : L+n+1+Q < i) (hi : i < F) : J i=none :=
    (old fr a b d i (by omega) (by omega)).trans (fr.gap i lo hi)
  have paid (i : Nat) (lo : L+n+1 < i) (hi : i ≤ L+n+1+Q) : J i=some true :=
    (old fr a b d i (by omega) (by have h:=fr.room; omega)).trans (fr.marks i lo hi)
  cases mode
  all_goals (have positive:=fr.paid; have room:=fr.room)
  case false =>
    obtain ⟨t,price,tr⟩ : ∃ t, t ≤ 8*(P+1) ∧ Path k P t ⟨Cursor.q k 360,D F r n 4,J⟩ ⟨Cursor.q k 368,D F r n 0,J⟩ := by run_tac travelTac 360 "368" 4 0
    have f:=K (k:=k) 368 369 (F+1) F J none .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) (atD fr a b d 0 (by omega)) (by run_tac rowTac) (by simp [dest])
    have g:=K (k:=k) 369 370 F (F-1) J (some false) .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Ffalse (by run_tac rowTac) rfl
    have gap:=sweepL (Cursor.q k 370) J (L+n+1+Q) (F-1-(L+n+1+Q)) (by change 370%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by intro i lo hi; rw [blank i lo (by omega)]; run_tac rowTac)
    rw [show L+n+1+Q+(F-1-(L+n+1+Q))=F-1 by omega] at gap
    have mark:=K (k:=k) 370 371 (L+n+1+Q) (L+n+Q) J (some true) .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) (paid _ (by omega) le_rfl) (by run_tac rowTac) (by simp [dest])
    have marks:=sweepL (Cursor.q k 371) J (L+n+1) (Q-1) (by change 371%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by intro i lo hi; rw [paid i lo (by omega)]; run_tac rowTac)
    rw [show L+n+1+(Q-1)=L+n+Q by omega] at marks
    have done:=K (k:=k) 371 343 (L+n+1) (L+n+1) J none .stay (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Hnone (by run_tac rowTac) rfl
    refine ⟨_,?_,tr.append f |>.append g |>.append gap |>.append mark |>.append marks |>.append done⟩
    dsimp only [P] at *; omega
  case true =>
    obtain ⟨t,price,tr⟩ : ∃ t, t ≤ 8*(P+1) ∧ Path k P t ⟨Cursor.q k 333,D F r n 3,J⟩ ⟨Cursor.q k 339,D F r n 0,J⟩ := by run_tac travelTac 333 "339" 3 0
    have f:=K (k:=k) 339 340 (F+1) F J none .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) (atD fr a b d 0 (by omega)) (by run_tac rowTac) (by simp [dest])
    have g:=K (k:=k) 340 341 F (F-1) J (some false) .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Ffalse (by run_tac rowTac) rfl
    have gap:=sweepL (Cursor.q k 341) J (L+n+1+Q) (F-1-(L+n+1+Q)) (by change 341%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by intro i lo hi; rw [blank i lo (by omega)]; run_tac rowTac)
    rw [show L+n+1+Q+(F-1-(L+n+1+Q))=F-1 by omega] at gap
    have mark:=K (k:=k) 341 342 (L+n+1+Q) (L+n+Q) J (some true) .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) (paid _ (by omega) le_rfl) (by run_tac rowTac) (by simp [dest])
    have marks:=sweepL (Cursor.q k 342) J (L+n+1) (Q-1) (by change 342%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by intro i lo hi; rw [paid i lo (by omega)]; run_tac rowTac)
    rw [show L+n+1+(Q-1)=L+n+Q by omega] at marks
    have done:=K (k:=k) 342 343 (L+n+1) (L+n+1) J none .stay (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Hnone (by run_tac rowTac) rfl
    refine ⟨_,?_,tr.append f |>.append g |>.append gap |>.append mark |>.append marks |>.append done⟩
    dsimp only [P] at *; omega
private theorem toBank {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (a b d : Nat) (mode : Bool) :
    let P:=F+5*r+n+7
    ∃ t, t ≤ 16*(P+1) ∧ Path k P t
      ⟨Cursor.q k (if mode then 373 else 346),L+n+1,I T L n F r a b d⟩
      ⟨Cursor.q k (if mode then 329 else 356),D F r n (if mode then 3 else 4),I T L n F r a b d⟩ := by
  dsimp only
  let P:=F+5*r+n+7; let J:=I T L n F r a b d
  have Hnone : J (L+n+1)=none := (old fr a b d _ (by omega) (by have h:=fr.room; omega)).trans fr.right
  have Ffalse : J F=some false := (old fr a b d _ (by have h:=fr.room; omega) (by omega)).trans fr.fence
  have corridor (i : Nat) (lo : L+n+1 < i) (hi : i < F) : J i=none ∨ J i=some true := by
    have eq:=old fr a b d i (by omega) (by omega)
    by_cases paid : i ≤ L+n+1+Q
    · exact Or.inr (eq.trans (fr.marks i lo paid))
    · exact Or.inl (eq.trans (fr.gap i (by omega) hi))
  have room:=fr.room
  cases mode
  case false =>
    have first:=K (k:=k) 346 347 (L+n+1) (L+n+2) J none .right (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Hnone (by run_tac rowTac) (by simp [dest])
    have scan:=sweepR (Cursor.q k 347) J (L+n+2) (F-(L+n+2)) (by change 347%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by intro i lo hi; rcases corridor i (by omega) (by omega) with h|h <;> rw [h] <;> run_tac rowTac)
    rw [show L+n+2+(F-(L+n+2))=F by have h:=fr.paid; omega] at scan
    have last:=K (k:=k) 347 348 F (F+1) J (some false) .right (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Ffalse (by run_tac rowTac) rfl
    obtain ⟨t,price,tr⟩ : ∃ t, t ≤ 8*(P+1) ∧ Path k P t ⟨Cursor.q k 348,D F r n 0,J⟩ ⟨Cursor.q k 356,D F r n 4,J⟩ := by run_tac travelTac 348 "356" 0 4
    refine ⟨_,?_,first.append scan |>.append last |>.append tr⟩
    dsimp only [P] at *; omega
  case true =>
    have first:=K (k:=k) 373 374 (L+n+1) (L+n+2) J none .right (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Hnone (by run_tac rowTac) (by simp [dest])
    have scan:=sweepR (Cursor.q k 374) J (L+n+2) (F-(L+n+2)) (by change 374%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by intro i lo hi; rcases corridor i (by omega) (by omega) with h|h <;> rw [h] <;> run_tac rowTac)
    rw [show L+n+2+(F-(L+n+2))=F by have h:=fr.paid; omega] at scan
    have last:=K (k:=k) 374 375 F (F+1) J (some false) .right (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Ffalse (by run_tac rowTac) rfl
    obtain ⟨t,price,tr⟩ : ∃ t, t ≤ 8*(P+1) ∧ Path k P t ⟨Cursor.q k 375,D F r n 0,J⟩ ⟨Cursor.q k 329,D F r n 3,J⟩ := by run_tac travelTac 375 "329" 0 3
    refine ⟨_,?_,first.append scan |>.append last |>.append tr⟩
    dsimp only [P] at *; omega
private theorem wipe {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (a b d : Nat) (hd : d ≤ n) :
    Path k (F+5*r+n+7) d ⟨Cursor.q k 372,L+n+1-d,I T L n F r a b d⟩
      ⟨Cursor.q k 372,L+n+1,I T L n F r a b 0⟩ := by
  have room:=fr.room
  induction d with
  | zero => simpa only [Nat.sub_zero] using Path.nil ⟨Cursor.q k 372,L+n+1,I T L n F r a b 0⟩ (by change L+n+1 ≤ F+5*r+n+7; omega)
  | succ d ih =>
    have step:=hop (P:=F+5*r+n+7) (Cursor.q k 372) (Cursor.q k 372) (L+n-d) (L+n+1-d)
      (I T L n F r a b (d+1)) (some false) .right
      (by change 372%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (by omega) (by omega)
      (by rw [assignment fr a b (d+1) _ (by omega) (by omega),decide_eq_true (by omega)]; run_tac rowTac) (by dsimp [dest]; omega)
    rw [unmark fr a b d (by omega)] at step
    rw [show L+n+1-(d+1)=L+n-d by omega]
    simpa only [Nat.add_comm] using step.append (ih (by omega))
private theorem picked {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (e : Nat) (he : e < n) :
    Path k (F+5*r+n+7) (2*e+3) ⟨Cursor.q k 343,L+n+1,I T L n F r 0 e e⟩
      ⟨Cursor.q k 346,L+n+1,I T L n F r 0 e (e+1)⟩ := by
  let P:=F+5*r+n+7; let J:=I T L n F r 0 e e
  have room:=fr.room
  have Hnone : J (L+n+1)=none := (old fr 0 e e _ (by omega) (by omega)).trans fr.right
  have first:=K (k:=k) 343 344 (L+n+1) (L+n) J none .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) Hnone (by run_tac rowTac) (by simp [dest])
  have scan:=sweepL (Cursor.q k 344) J (L+n-e) e (by change 344%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by
    intro i lo hi; dsimp only [J]; rw [assignment fr 0 e e i (by omega) (by omega),decide_eq_true (by omega)]; run_tac rowTac)
  rw [show L+n-e+e=L+n by omega] at scan
  have take:=hop (P:=P) (Cursor.q k 344) (Cursor.q k 345) (L+n-e) (L+n+1-e) J (some true) .right
    (by change 344%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (by dsimp [P]; omega) (by dsimp [P]; omega)
    (by dsimp only [J]; rw [assignment fr 0 e e _ (by omega) (by omega),decide_eq_false (by omega)]; run_tac rowTac) (by dsimp [dest]; omega)
  dsimp only [J] at take
  rw [mark fr 0 e e he] at take
  have send:=sweepR (Cursor.q k 345) (I T L n F r 0 e (e+1)) (L+n+1-e) e
    (by change 345%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by
      intro i lo hi; rw [assignment fr 0 e (e+1) i (by omega) (by omega)]; cases decide (L+n+1-(e+1) ≤ i) <;> run_tac rowTac)
  rw [show L+n+1-e+e=L+n+1 by omega] at send
  have last:=K (k:=k) 345 346 (L+n+1) (L+n+1) (I T L n F r 0 e (e+1)) none .stay (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    ((old fr 0 e (e+1) _ (by omega) (by omega)).trans fr.right) (by run_tac rowTac) rfl
  simpa only [show 1+e+1+e+1=2*e+3 by omega] using first.append scan |>.append take |>.append send |>.append last
private theorem copyIter {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (e : Nat) (en : e < n) (er : e ≤ r) :
    let P:=F+5*r+n+7
    ∃ t, t ≤ 64*(P+1) ∧
      (if e < r then Path k P t ⟨Cursor.q k 343,L+n+1,I T L n F r 0 e e⟩
          ⟨Cursor.q k 343,L+n+1,I T L n F r 0 (e+1) (e+1)⟩
       else Path k P t ⟨Cursor.q k 343,L+n+1,I T L n F r 0 e e⟩
          ⟨Cursor.q k (798+93*k),D F r n 0,I T L n F r 0 r (r+1)⟩) := by
  dsimp only
  let P:=F+5*r+n+7
  have a:=picked T fr hk e en
  obtain ⟨u,pu,outbound⟩:=toBank T fr hk 0 e (e+1) false
  let J:=I T L n F r 0 e (e+1)
  have c:=inc (k:=k) (P:=P) 356 360 403 (D F r n 4) r e J (by omega) (by dsimp [D,P]; omega) er
    (atD fr 0 e (e+1) 4 (by omega)) (by rw [show D F r n 4+r+1=D F r n 5 by dsimp [D]; omega]; exact atD fr 0 e (e+1) 5 (by omega))
    (by intro i lo hi; exact unary4 fr 0 e (e+1) i lo (by dsimp [D] at *; omega))
    (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
    (by intro bit; cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
  by_cases more : e < r
  · simp only [if_pos more] at c
    rw [set4 fr 0 e (e+1) more] at c
    obtain ⟨v,pv,d⟩:=backH T fr hk 0 (e+1) (e+1) false
    refine ⟨(2*e+3)+u+(2*e+3)+v,?_,?_⟩
    · dsimp only [P] at *; omega
    · rw [if_pos more]; exact a.append outbound |>.append c |>.append d
  · have eq : e=r := by omega
    simp only [if_neg more] at c
    let a:=0; let b:=e; let d:=e+1
    obtain ⟨v,pv,endPath⟩ : ∃ v, v ≤ 8*(P+1) ∧ Path k P v
        ⟨Cursor.q k 403,D F r n 4,J⟩ ⟨Cursor.q k (798+93*k),D F r n 0,J⟩ := by
      run_tac travelTac 403 "798+93*k" 4 0
    refine ⟨(2*e+3)+u+(2*e+3)+v,?_,?_⟩
    · dsimp only [P] at *; omega
    · rw [if_neg more]; simpa only [J,eq] using (picked T fr hk e en).append outbound |>.append c |>.append endPath
private theorem widthDone {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) :
    let P:=F+5*r+n+7
    ∃ t, t ≤ 32*(P+1) ∧ Path k P t ⟨Cursor.q k 343,L+n+1,I T L n F r 0 n n⟩
      ⟨Cursor.q k 329,D F r n 3,I T L n F r 0 n 0⟩ := by
  dsimp only
  let P:=F+5*r+n+7; let J:=I T L n F r 0 n n
  have room:=fr.room
  have hnone : J (L+n+1)=none := (old fr 0 n n _ (by omega) (by omega)).trans fr.right
  have a:=K (k:=k) 343 344 (L+n+1) (L+n) J none .left (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega) hnone (by run_tac rowTac) (by simp [dest])
  have b:=sweepL (Cursor.q k 344) J L n (by change 344%Cursor.stateCount k < 411; rw [small_mod _ _ (by omega)]; omega) (P:=P) (by dsimp [P]; omega) (by
    intro i lo hi; dsimp only [J]; rw [assignment fr 0 n n i lo (by omega),decide_eq_true (by omega)]; run_tac rowTac)
  have c:=K (k:=k) 344 372 L (L+1) J none .right (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    ((old fr 0 n n _ (by omega) (by omega)).trans fr.sep) (by run_tac rowTac) rfl
  have d:=wipe T fr hk 0 n n le_rfl
  rw [show L+n+1-n=L+1 by omega] at d
  have e:=K (k:=k) 372 373 (L+n+1) (L+n+1) (I T L n F r 0 n 0) none .stay (by omega) (P:=P) (by dsimp [P]; omega) (by dsimp [P]; omega)
    ((old fr 0 n 0 _ (by omega) (by omega)).trans fr.right) (by run_tac rowTac) rfl
  obtain ⟨v,pv,f⟩:=toBank T fr hk 0 n 0 true
  refine ⟨_,?_,a.append b |>.append c |>.append d |>.append e |>.append f⟩
  dsimp only [P] at *; omega
private theorem zeroClock (P t : Nat) (h : t ≤ 32*(P+1)) : t ≤ 128*(0+1)*(P+1) := by omega
private theorem moreClock (P v a b : Nat) (ha : a ≤ 64*(P+1)) (hb : b ≤ 128*(v+1)*(P+1)) :
    a+b ≤ 128*(v+1+1)*(P+1) := by nlinarith only [ha,hb,Nat.zero_le P]
private theorem capClock (P v a : Nat) (ha : a ≤ 64*(P+1)) : a ≤ 128*(v+1+1)*(P+1) := by
  nlinarith only [ha,Nat.zero_le P,Nat.zero_le v,Nat.zero_le (v*P)]
private theorem copyLoop {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (e v : Nat) (sum : e+v=n) (er : e ≤ r) :
    let P:=F+5*r+n+7
    ∃ t, t ≤ 128*(v+1)*(P+1) ∧ Path k P t
      ⟨Cursor.q k 343,L+n+1,I T L n F r 0 e e⟩
      ⟨Cursor.q k (if n ≤ r then 329 else 798+93*k),
        (if n ≤ r then D F r n 3 else D F r n 0),
        (if n ≤ r then I T L n F r 0 n 0 else I T L n F r 0 r (r+1))⟩ := by
  dsimp only
  let P:=F+5*r+n+7
  induction v generalizing e with
  | zero =>
    have eq : e=n := by omega
    subst e
    obtain ⟨t,price,path⟩:=widthDone T fr hk
    exact ⟨t,zeroClock P t price,by simpa only [if_pos er] using path⟩
  | succ v ih =>
    obtain ⟨a,pa,part⟩:=copyIter T fr hk e (by omega) er
    by_cases more : e < r
    · rw [if_pos more] at part
      obtain ⟨b,pb,tail⟩:=ih (e+1) (by omega) (by omega)
      exact ⟨a+b,moreClock P v a b pa pb,part.append tail⟩
    · rw [if_neg more] at part
      have cap : ¬n ≤ r := by omega
      exact ⟨a,capClock P v a pa,by simpa only [if_neg cap] using part⟩
private theorem transfer {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (v a : Nat) (room : a+v ≤ r) :
    let P:=F+5*r+n+7
    ∃ t, t ≤ 128*(v+1)*(P+1) ∧ Path k P t ⟨Cursor.q k 383,D F r n 4,I T L n F r a v 0⟩
      ⟨Cursor.q k 411,D F r n 3,I T L n F r (a+v) 0 0⟩ := by
  dsimp only
  let P:=F+5*r+n+7
  induction v generalizing a with
  | zero =>
    have c:=dec (k:=k) (P:=P) 383 387 401 (D F r n 4) r 0 (I T L n F r a 0 0) (by omega) (by dsimp [D,P]; omega) (by omega)
      (atD fr a 0 0 4 (by omega)) (by rw [show D F r n 4+r+1=D F r n 5 by dsimp [D]; omega]; exact atD fr a 0 0 5 (by omega))
      (by intro i lo hi; exact unary4 fr a 0 0 i lo (by dsimp [D] at *; omega))
      (by run_tac rowTac) (by run_tac rowTac)
      (by intro sym neq; cases sym with | none => run_tac rowTac | some bit => cases bit with | false => run_tac rowTac | true => exact (neq rfl).elim)
      (by run_tac rowTac) (by intro bit; cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
    simp only [Nat.mul_zero,Nat.zero_add,↓reduceIte] at c
    let b:=0; let d:=0
    obtain ⟨u,pu,tr⟩ : ∃ u, u ≤ 8*(P+1) ∧ Path k P u ⟨Cursor.q k 401,D F r n 4,I T L n F r a b d⟩ ⟨Cursor.q k 411,D F r n 3,I T L n F r a b d⟩ := by run_tac travelTac 401 "411" 4 3
    exact ⟨3+u,by dsimp only [P] at *; omega,by simpa only [Nat.add_zero] using c.append tr⟩
  | succ v ih =>
    have c:=dec (k:=k) (P:=P) 383 387 401 (D F r n 4) r (v+1) (I T L n F r a (v+1) 0) (by omega) (by dsimp [D,P]; omega) (by omega)
      (atD fr a (v+1) 0 4 (by omega)) (by rw [show D F r n 4+r+1=D F r n 5 by dsimp [D]; omega]; exact atD fr a (v+1) 0 5 (by omega))
      (by intro i lo hi; exact unary4 fr a (v+1) 0 i lo (by dsimp [D] at *; omega))
      (by run_tac rowTac) (by run_tac rowTac)
      (by intro sym neq; cases sym with | none => run_tac rowTac | some bit => cases bit with | false => run_tac rowTac | true => exact (neq rfl).elim)
      (by run_tac rowTac) (by intro bit; cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
    simp only [if_neg (by omega : v+1≠0)] at c
    rw [show D F r n 4+(v+1)=D F r n 4+v+1 by omega,unset4 fr a v 0 (by omega)] at c
    let b:=v; let d:=0
    obtain ⟨u,pu,tr⟩ : ∃ u, u ≤ 8*(P+1) ∧ Path k P u ⟨Cursor.q k 387,D F r n 4,I T L n F r a b d⟩ ⟨Cursor.q k 389,D F r n 3,I T L n F r a b d⟩ := by run_tac travelTac 387 "389" 4 3
    have h:=inc (k:=k) (P:=P) 389 393 395 (D F r n 3) r a (I T L n F r a v 0) (by omega) (by dsimp [D,P]; omega) (by omega)
      (atD fr a v 0 3 (by omega)) (by rw [show D F r n 3+r+1=D F r n 4 by dsimp [D]; omega]; exact atD fr a v 0 4 (by omega))
      (by intro i lo hi; exact unary3 fr a v 0 i lo (by dsimp [D] at *; omega))
      (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
      (by intro bit; cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
    simp only [if_pos (by omega : a < r)] at h
    rw [set3 fr a v 0 (by omega)] at h
    have ret : ∃ z, z ≤ 8*(P+1) ∧ Path k P z ⟨Cursor.q k 393,D F r n 3,I T L n F r (a+1) v 0⟩ ⟨Cursor.q k 383,D F r n 4,I T L n F r (a+1) v 0⟩ := by
      let a:=a+1; run_tac travelTac 393 "383" 3 4
    obtain ⟨z,pz,ret⟩:=ret
    obtain ⟨w,pw,tail⟩:=ih (a+1) (by omega)
    refine ⟨(2*(v+1)+3)+u+(2*a+3)+z+w,?_,?_⟩
    · have cap : r ≤ P := by dsimp [P]; omega
      try dsimp only [P] at *
      nlinarith only [pu,pz,pw,room,cap,Nat.zero_le a,Nat.zero_le v]
    · simpa only [show a+1+v=a+(v+1) by omega] using c.append tr |>.append h |>.append ret |>.append tail
private theorem core {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (hk : 0 < k) (hr : 0 < r) :
    let P:=F+5*r+n+7
    ∃ t, t ≤ 1024*(n+r+1)^2*(P+2) ∧ Path k P t ⟨Cursor.q k 329,D F r n 3,T⟩
      ⟨Cursor.q k (if n ≤ r then 411 else 798+93*k),
        (if n ≤ r then D F r n 3 else D F r n 0),
        I T L n F r (if n ≤ r then n else 0) (if n ≤ r then 0 else r) (if n ≤ r then 0 else r+1)⟩ := by
  dsimp only
  let P:=F+5*r+n+7
  have c:=dec (k:=k) (P:=P) 329 333 381 (D F r n 3) r 1 (I T L n F r 1 0 0) (by omega) (by dsimp [D,P]; omega) hr
    (atD fr 1 0 0 3 (by omega)) (by rw [show D F r n 3+r+1=D F r n 4 by dsimp [D]; omega]; exact atD fr 1 0 0 4 (by omega))
    (by intro i lo hi; exact unary3 fr 1 0 0 i lo (by dsimp [D] at *; omega))
    (by run_tac rowTac) (by run_tac rowTac)
    (by intro sym neq; cases sym with | none => run_tac rowTac | some bit => cases bit with | false => run_tac rowTac | true => exact (neq rfl).elim)
    (by run_tac rowTac) (by intro bit; cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
  simp only [if_neg (by decide : ¬1=0)] at c
  rw [show D F r n 3+1=D F r n 3+0+1 by omega,unset3 fr 0 0 0 hr,initial_image fr] at c
  obtain ⟨u,pu,back⟩:=backH T fr hk 0 0 0 true
  obtain ⟨v,pv,copy⟩:=copyLoop T fr hk 0 n (by omega) (by omega)
  by_cases fits : n ≤ r
  · simp only [if_pos fits] at copy
    have z:=dec (k:=k) (P:=P) 329 333 381 (D F r n 3) r 0 (I T L n F r 0 n 0) (by omega) (by dsimp [D,P]; omega) (by omega)
      (atD fr 0 n 0 3 (by omega)) (by rw [show D F r n 3+r+1=D F r n 4 by dsimp [D]; omega]; exact atD fr 0 n 0 4 (by omega))
      (by intro i lo hi; exact unary3 fr 0 n 0 i lo (by dsimp [D] at *; omega))
      (by run_tac rowTac) (by run_tac rowTac)
      (by intro sym neq; cases sym with | none => run_tac rowTac | some bit => cases bit with | false => run_tac rowTac | true => exact (neq rfl).elim)
      (by run_tac rowTac) (by intro bit; cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
    simp only [Nat.mul_zero,Nat.zero_add,↓reduceIte] at z
    let a:=0; let b:=n; let d:=0
    obtain ⟨w,pw,tr⟩ : ∃ w, w ≤ 8*(P+1) ∧ Path k P w ⟨Cursor.q k 381,D F r n 3,I T L n F r a b d⟩ ⟨Cursor.q k 383,D F r n 4,I T L n F r a b d⟩ := by run_tac travelTac 381 "383" 3 4
    obtain ⟨y,py,tail⟩:=transfer T fr hk n 0 (by omega)
    refine ⟨5+u+v+3+w+y,?_,?_⟩
    · have cap : r ≤ P := by dsimp [P]; omega
      try dsimp only [P] at *
      nlinarith only [pu,pv,pw,py,cap,Nat.zero_le n,Nat.zero_le r,Nat.zero_le (n*r),Nat.zero_le (P*n*r),Nat.zero_le (n^2),Nat.zero_le (r^2),Nat.zero_le (P*n^2),Nat.zero_le (P*r^2),Nat.zero_le (P*n),Nat.zero_le (P*r)]
    · simp only [if_pos fits]
      simpa only [Nat.zero_add] using c.append back |>.append copy |>.append z |>.append tr |>.append tail
  · simp only [if_neg fits] at copy
    refine ⟨5+u+v,?_,?_⟩
    · try dsimp only [P] at *
      nlinarith only [pu,pv,Nat.zero_le n,Nat.zero_le r,Nat.zero_le P,Nat.zero_le (n*r),Nat.zero_le (P*n*r),Nat.zero_le (n^2),Nat.zero_le (r^2),Nat.zero_le (P*n^2),Nat.zero_le (P*r^2),Nat.zero_le (P*n),Nat.zero_le (P*r)]
    · simp only [if_neg fits]; exact c.append back |>.append copy
/-- Literal first power block, including zero width and its real capped exit. -/
theorem first_product (k N B L n Q F r : Nat) (T : Nat → Option Bool) (hk : 0 < k) (hr : 0 < r)
    (paid : 0 < Q) (room : L+n+1+Q < F) (sep : T L=none) (right : T (L+n+1)=none)
    (marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → T i=some true)
    (gap : ∀ i, L+n+1+Q < i → i < F → T i=none) (fence : T F=some false)
    (delims : ∀ i, i=F+1 ∨ i=F+r+2 ∨ i=F+r+n+3 ∨ i=F+2*r+n+4 ∨
      i=F+3*r+n+5 ∨ i=F+4*r+n+6 ∨ i=F+5*r+n+7 → T i=none)
    (b0 : ∀ i, F+1 < i → i < F+r+2 → T i=some true)
    (b1 : ∀ i, F+r+2 < i → i < F+r+n+3 → T i=some false)
    (initial : Target.image T L n F r (Pnp4.Frontier.ContractExpansion.bitLength n) 1 0 0 0=T) :
    Target.FirstProduct k N B L n F r T := by
  have fr : Frame T L n Q F r := by
    refine ⟨paid,room,sep,right,marks,gap,fence,?_,?_,?_⟩
    · intro j hj
      apply delims (D F r n j)
      interval_cases j <;> simp [D]
    · intro j hj i lo hi
      interval_cases j
      all_goals norm_num only [D] at lo hi ⊢
      all_goals simp only [↓reduceIte]
      case «0» => rw [b0 i lo hi,decide_eq_true (by omega)]
      case «1» => rw [b1 i lo hi,decide_eq_false (by omega)]
      all_goals
        have eq : Target.image T L n F r (Pnp4.Frontier.ContractExpansion.bitLength n) 1 0 0 0 i=T i := congrArg (fun X : Nat → Option Bool => X i) initial
        rw [← eq]
        dsimp only [Target.image]
        split_ifs <;> first | rfl | omega
    · intro i lo hi
      have eq : Target.image T L n F r (Pnp4.Frontier.ContractExpansion.bitLength n) 1 0 0 0 i=T i := congrArg (fun X : Nat → Option Bool => X i) initial
      rw [← eq]
      dsimp only [Target.image]
      rw [if_pos ⟨lo,hi⟩,decide_eq_false (by omega)]
  intro fit
  obtain ⟨t,price,path⟩:=core T fr hk hr
  refine ⟨t,price,?_,?_⟩
  · have ex:=path.execute fit
    simpa only [embed,D,I] using ex
  · exact path.first fit
end CappedWeight
