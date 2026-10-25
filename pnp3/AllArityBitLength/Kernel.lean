import AllArityBitLength.Rows
namespace AllArityBitLength
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
  safe : c.state.val < 329
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
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hs : s.val < 329) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hs,hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hs : s.val < 329) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hs hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (hs : s.val < 329) (fit : h+r   ≤   P) (rows : ∀ i, h   ≤   i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right hs (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (hs : s.val < 329) (fit : low+r   ≤   P) (rows : ∀ i, low < i → i   ≤   low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left hs (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private theorem Path.first {k N B P t c d} (path : Path k P t c d) (hp : P < tapeLength N B)
    (u : Nat) (hu : u < t) :
    ((Cursor.machine k).run u (embed (N := N) (B := B) c (lt_of_le_of_lt path.bounds.1 hp))).state.val < 329 := by
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
elab "seedRow" : tactic => withMainContext do
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
  let term ← Lean.Meta.mkAppM ``AllArityBitLength.phase_row #[stateArgs[0]!,src,code,args[2]!]; let goals ← goal.apply term
  replaceMainGoal goals
  evalTactic (← `(tactic| all_goals first | rfl | decide | omega))
private theorem K {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (mv : Move)
    (safe : s < 329) (hb : h ≤ P) (ha : h' ≤ P) (value : T h=b)
    (row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k d,b,mv)) (hm : dest h mv=h') :
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ := by
  apply keep _ _ _ _ _ _ ?_ hb ha (by rw [value]; exact row) hm
  simpa only [Cursor.q,small_mod k s (by omega)] using safe
/-- Existing literal q308..q328 seed path. Values of occupied banks are preserved. -/
theorem seed (k N B L n Q F r : Nat) (T : Nat → Option Bool)
    (hr : 0 < r) (room : L+n+1+Q < F) (sep : T L=none)
    (assn : ∀ i, L < i → i < L+n+1 → ∃ b, T i=some b) (right : T (L+n+1)=none)
    (corridor : ∀ i, L+n+1 < i → i < F → T i=none ∨ T i=some true)
    (fence : T F=some false) (d0 : T (F+1)=none)
    (b0 : ∀ i, F+1 < i → i < F+r+2 → ∃ b, T i=some b) (d1 : T (F+r+2)=none)
    (b1 : ∀ i, F+r+2 < i → i < F+r+n+3 → ∃ b, T i=some b) (d2 : T (F+r+n+3)=none)
    (b2 : ∀ i, F+r+n+3 < i → i < F+2*r+n+4 → ∃ b, T i=some b) (d3 : T (F+2*r+n+4)=none)
    (empty : T (F+2*r+n+5)=some false) (fit : F+5*r+n+7 < tapeLength N B) :
    ∃ t, t ≤ 16*(F+5*r+n+8) ∧
      (Cursor.machine k).run t (⟨Cursor.q k 308,⟨L,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)=
        ⟨Cursor.q k 329,⟨F+2*r+n+4,by omega⟩,fun i => Target.seedImage T F r n i.val⟩ ∧
      (∀ u, u < t → ((Cursor.machine k).run u
        (⟨Cursor.q k 308,⟨L,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 329) := by
  let P := F+5*r+n+7
  let H := L+n+1
  let D1 := F+r+2
  let D2 := F+r+n+3
  let D3 := F+2*r+n+4
  have a := K (k:=k) (P:=P) 308 309 L (L+1) T none .right (by omega) (by omega) (by omega) sep (by seedRow) rfl
  have b := sweepR (Cursor.q k 309) T (L+1) n (by rw [show (Cursor.q k 309).val=309 from small_mod k 309 (by omega)]; omega) (P:=P) (by omega) (by
    intro i lo hi; obtain ⟨b,hb⟩ := assn i (by omega) (by omega); rw [hb]; cases b <;> seedRow)
  rw [show L+1+n=H by dsimp [H]; omega] at b
  have c := K (k:=k) (P:=P) 309 310 H H T none .stay (by omega) (by omega) (by omega) right (by seedRow) rfl
  have d := K (k:=k) (P:=P) 310 311 H (H+1) T none .right (by omega) (by omega) (by omega) right (by seedRow) rfl
  have e := sweepR (Cursor.q k 311) T (H+1) (F-(H+1)) (by rw [show (Cursor.q k 311).val=311 from small_mod k 311 (by omega)]; omega) (P:=P) (by omega) (by
    intro i lo hi
    rcases corridor i (by dsimp [H] at lo; omega) (by omega) with hb|hb
    · rw [hb]; seedRow
    · rw [hb]; seedRow)
  rw [show H+1+(F-(H+1))=F by dsimp [H] at *; omega] at e
  have f := K (k:=k) (P:=P) 311 312 F (F+1) T (some false) .right (by omega) (by omega) (by omega) fence (by seedRow) rfl
  have g := K (k:=k) (P:=P) 312 313 (F+1) (F+2) T none .right (by omega) (by omega) (by omega) d0 (by seedRow) rfl
  have h := sweepR (Cursor.q k 313) T (F+2) r (by rw [show (Cursor.q k 313).val=313 from small_mod k 313 (by omega)]; omega) (P:=P) (by omega) (by
    intro i lo hi; obtain ⟨b,hb⟩ := b0 i (by omega) (by omega); rw [hb]; cases b <;> seedRow)
  rw [show F+2+r=D1 by dsimp [D1]; omega] at h
  have i := K (k:=k) (P:=P) 313 314 D1 D1 T none .stay (by omega) (by omega) (by omega) d1 (by seedRow) rfl
  have j := K (k:=k) (P:=P) 314 315 D1 (D1+1) T none .right (by omega) (by omega) (by omega) d1 (by seedRow) rfl
  have l := sweepR (Cursor.q k 315) T (D1+1) n (by rw [show (Cursor.q k 315).val=315 from small_mod k 315 (by omega)]; omega) (P:=P) (by dsimp [D1,P]; omega) (by
    intro i lo hi; obtain ⟨b,hb⟩ := b1 i (by dsimp [D1] at lo; omega) (by dsimp [D1] at hi; omega); rw [hb]; cases b <;> seedRow)
  rw [show D1+1+n=D2 by dsimp [D1,D2]; omega] at l
  have m := K (k:=k) (P:=P) 315 316 D2 D2 T none .stay (by omega) (by dsimp [D2,P]; omega) (by dsimp [D2,P]; omega) d2 (by seedRow) rfl
  have o := K (k:=k) (P:=P) 316 317 D2 (D2+1) T none .right (by omega) (by dsimp [D2,P]; omega) (by dsimp [D2,P]; omega) d2 (by seedRow) rfl
  have p := sweepR (Cursor.q k 317) T (D2+1) r (by rw [show (Cursor.q k 317).val=317 from small_mod k 317 (by omega)]; omega) (P:=P) (by dsimp [D2,P]; omega) (by
    intro i lo hi; obtain ⟨b,hb⟩ := b2 i (by dsimp [D2] at lo; omega) (by dsimp [D2] at hi; omega); rw [hb]; cases b <;> seedRow)
  rw [show D2+1+r=D3 by dsimp [D2,D3]; omega] at p
  have q := K (k:=k) (P:=P) 317 318 D3 D3 T none .stay (by omega) (by dsimp [D3,P]; omega) (by dsimp [D3,P]; omega) d3 (by seedRow) rfl
  have s := K (k:=k) (P:=P) 318 319 D3 (D3+1) T none .right (by omega) (by dsimp [D3,P]; omega) (by dsimp [D3,P]; omega) d3 (by seedRow) rfl
  have v := hop (P:=P) (Cursor.q k 319) (Cursor.q k 320) (D3+1) D3 T (some true) .left
    (by rw [show (Cursor.q k 319).val=319 from small_mod k 319 (by omega)]; omega)
    (by dsimp [D3,P]; omega) (by dsimp [D3,P]; omega) (by rw [empty]; seedRow) (by simp [dest])
  let Z := put T (D3+1) (some true)
  have zd : Z D3=none := by dsimp only [Z,put]; rw [if_neg (by omega)]; exact d3
  have w := K (k:=k) (P:=P) 320 328 D3 D3 Z none .stay (by omega) (by dsimp [D3,P]; omega) (by dsimp [D3,P]; omega) zd (by seedRow) rfl
  have y := K (k:=k) (P:=P) 328 329 D3 D3 Z none .stay (by omega) (by dsimp [D3,P]; omega) (by dsimp [D3,P]; omega) zd (by seedRow) rfl
  have path := a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h |>.append i |>.append j |>.append l |>.append m |>.append o |>.append p |>.append q |>.append s |>.append v |>.append w |>.append y
  have zeq : Z=Target.seedImage T F r n := by
    funext i; rfl
  let tt := 1+n+1+1+(F-(H+1))+1+1+r+1+1+n+1+1+r+1+1+1+1+1
  refine ⟨tt,?_,?_,?_⟩
  · dsimp only [tt,H]; omega
  · have ex := path.execute fit
    simpa only [embed,zeq] using ex
  · exact path.first fit
end AllArityBitLength
