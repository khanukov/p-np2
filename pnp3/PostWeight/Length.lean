import PostWeight.Kernel
namespace PostWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private structure Node (k : Nat) where
  state : Fin (Cursor.stateCount k)
  head : Nat
  tape : Nat → Option Bool
private abbrev KernelNode (k : Nat) : Type := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Node" => exact OLD k
private def toOld {k : Nat} (c : Node k) : KernelNode k := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Node.mk" => exact OLD c.state c.head c.tape
private abbrev Banks (T : Nat → Option Bool) (L n F r : Nat) : Prop := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Banks" => exact OLD T L n F r
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def I (T : Nat → Option Bool) (L n F r a b c d : Nat) : Nat → Option Bool :=
  CappedWeight.Target.image T L n F r a b c d 0
private abbrev Path (k P t : Nat) (c d : Node k) : Prop := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Path" => exact OLD k P t (toOld c) (toOld d)
private def rowTac : TacticM Unit := by
  fromDonor "PostWeight.Rows" "PostWeight" "rowTac" => exact (id OLD)
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i=h then b else T i
private def dest (h : Nat) : Move → Nat
  | .left => h-1 | .stay => h | .right => h+1
private def val (a b c d j : Nat) : Nat := if j=2 then a else if j=3 then b else if j=4 then c else d
namespace Path
private theorem nil {k P : Nat} (c : Node k) (hp : c.head ≤ P) : Path k P 0 c c := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Path.nil" => exact OLD (toOld c) hp
private theorem append {k P t u c d e} (h : Path k P t c d) (g : Path k P u d e) : Path k P (t+u) c e := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Path.append" => exact OLD h g
end Path
private abbrev hop : ∀ {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (_hb : h ≤ P) (_ha : h' ≤ P)
    (_row : (Cursor.machine k).step s (T h) = (s',b,m)) (_hm : dest h m = h'),
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "hop" => exact (id OLD)
private abbrev sweepR : ∀ {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (_fit : h+r ≤ P) (_rows : ∀ i, h ≤ i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)),
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "sweepR" => exact (id OLD)
private abbrev sweepL : ∀ {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (_fit : low+r ≤ P) (_rows : ∀ i, low < i → i ≤ low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)),
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "sweepL" => exact (id OLD)
private abbrev K : ∀ {k P : Nat} (s _d h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (mv : Move)
    (_hb : h ≤ P) (_ha : h' ≤ P) (_cell : T h=b)
    (_row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k _d,b,mv)) (_hm : dest h mv=h'),
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k _d,h',T⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "K" => exact (id OLD)
private abbrev inc : ∀ {k P : Nat} (s yes no base w v : Nat) (T : Nat → Option Bool)
    (_fit : base+w+1 ≤ P) (_hv : v ≤ w) (_sep : T base=none) (_endD : T (base+w+1)=none)
    (_unary : ∀ i, base < i → i < base+w+1 → T i=some (decide (i ≤ base+v)))
    (_entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (_scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right))
    (_add : (Cursor.machine k).step (Cursor.q k (s+1)) (some false)=(Cursor.q k (s+2),some true,.left))
    (_full : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+3),none,.left))
    (_back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+2)) (some b)=(Cursor.q k (s+2),some b,.left))
    (_ok : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k yes,none,.stay))
    (_bad : (Cursor.machine k).step (Cursor.q k (s+3)) (some true)=(Cursor.q k (s+3),some true,.left))
    (_over : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k no,none,.stay)),
    Path k P (2*v+3) ⟨Cursor.q k s,base,T⟩
      ⟨Cursor.q k (if v < w then yes else no),base,if v < w then put T (base+v+1) (some true) else T⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "inc" => exact (id OLD)
private abbrev crossR : ∀ {k P : Nat} (s _scan out low width : Nat) (T : Nat → Option Bool)
    (_fit : low+width+1 ≤ P)
    (_d : T low=none) (_endD : T (low+width+1)=none)
    (_occ : ∀ i, low < i → i < low+width+1 → ∃ b, T i=some b)
    (_entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k _scan,none,.right))
    (_body : ∀ b, (Cursor.machine k).step (Cursor.q k _scan) (some b)=(Cursor.q k _scan,some b,.right))
    (_exit : (Cursor.machine k).step (Cursor.q k _scan) none=(Cursor.q k out,none,.stay)),
    Path k P (width+2) ⟨Cursor.q k s,low,T⟩ ⟨Cursor.q k out,low+width+1,T⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "crossR" => exact (id OLD)
private abbrev crossL : ∀ {k P : Nat} (s _scan out low width : Nat) (T : Nat → Option Bool)
    (_fit : low+width+1 ≤ P)
    (_d : T low=none) (_endD : T (low+width+1)=none)
    (_occ : ∀ i, low < i → i < low+width+1 → ∃ b, T i=some b)
    (_entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k _scan,none,.left))
    (_body : ∀ b, (Cursor.machine k).step (Cursor.q k _scan) (some b)=(Cursor.q k _scan,some b,.left))
    (_exit : (Cursor.machine k).step (Cursor.q k _scan) none=(Cursor.q k out,none,.stay)),
    Path k P (width+2) ⟨Cursor.q k s,low+width+1,T⟩ ⟨Cursor.q k out,low,T⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "crossL" => exact (id OLD)
private abbrev atD : ∀ {T L n F r} (_fr : Banks T L n F r) (a b c _d j : Nat) (_hj : j ≤ 6),
    I T L n F r a b c _d (D F r n j)=none := by
  fromDonor "PostWeight.Kernel" "PostWeight" "atD" => exact (id OLD)
private abbrev atBank : ∀ {T L n F r} (_fr : Banks T L n F r) (a b c _d j i : Nat)
    (_hj : 2 ≤ j) (_hj' : j < 6) (_lo : D F r n j < i) (_hi : i < D F r n (j+1)),
    I T L n F r a b c _d i=some (decide (i ≤ D F r n j+val a b c _d j)) := by
  fromDonor "PostWeight.Kernel" "PostWeight" "atBank" => exact (id OLD)
private abbrev Dstep : ∀ (F r n j : Nat) (_lo : 2 ≤ j) (_hi : j < 6),
    D F r n (j+1)=D F r n j+r+1 := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Dstep" => exact (id OLD)
private abbrev Dbound : ∀ (F r n j P : Nat) (_hj : j ≤ 6) (_fit : D F r n 6 ≤ P),
    D F r n j ≤ P := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Dbound" => exact (id OLD)
private abbrev preparation : ∀ {k P T L n F r} (_fr : Banks T L n F r) (_fit : D F r n 6 ≤ P)
    (g W : Nat) (_room : W ≤ r),
    ∃ t, t ≤ 512*(W+1)*(P+1) ∧ Path k P t
      ⟨Cursor.q k (430+93*k),D F r n 2,I T L n F r 0 g W 0⟩
      ⟨Cursor.q k (482+93*k),D F r n 4,I T L n F r 0 0 W W⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "preparation" => exact (id OLD)
private abbrev leftI : ∀ {k P T L n F r} (_fr : Banks T L n F r) (_fit : D F r n 6 ≤ P)
    (s out a b c _d j : Nat) (_lo : 2 ≤ j) (_hi : j < 6)
    (_entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.left))
    (_scan : ∀ v, (Cursor.machine k).step (Cursor.q k (s+1)) (some v)=(Cursor.q k (s+1),some v,.left))
    (_exit : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k out,none,.stay)),
    Path k P (r+2) ⟨Cursor.q k s,D F r n (j+1),I T L n F r a b c _d⟩
      ⟨Cursor.q k out,D F r n j,I T L n F r a b c _d⟩ := by
  fromDonor "PostWeight.Kernel" "PostWeight" "leftI" => exact (id OLD)
private theorem banks_room {T L n F r} (fr : Banks T L n F r) : L+n+1 < F := by
  fromDonor "PostWeight.Kernel" "PostWeight" "Banks.room" => exact OLD fr
private def J (T : Nat → Option Bool) (L n F r W a0 a1 b0 b1 j : Nat) : Nat → Option Bool := fun i =>
  if D F r n 3 < i ∧ i < D F r n 4 then some (decide (D F r n 3+a0 < i ∧ i ≤ D F r n 3+a1)) else
  if D F r n 4 < i ∧ i < D F r n 5 then some (decide (D F r n 4+b0 < i ∧ i ≤ D F r n 4+b1)) else
  I T L n F r j 0 0 W i
private def phase (T : Nat → Option Bool) (L n F r W : Nat) (side : Bool) (v u c j : Nat) : Nat → Option Bool :=
  if side then J T L n F r W u v 0 c j else J T L n F r W 0 c u v j
private def lab (side : Bool) (a b : Nat) := if side then b else a
private def source (F r n : Nat) (side : Bool) := D F r n (if side then 3 else 4)
private theorem phaseD {T L n F r} (fr : Banks T L n F r) (W v u c j h : Nat) (side : Bool) (hh : h ≤ 6) :
    phase T L n F r W side v u c j (D F r n h)=none := by
  have a : ¬(D F r n 3 < D F r n h ∧ D F r n h < D F r n 4) := by
    interval_cases h <;> dsimp [D] <;> omega
  have b : ¬(D F r n 4 < D F r n h ∧ D F r n h < D F r n 5) := by
    interval_cases h <;> dsimp [D] <;> omega
  cases side <;> simp only [phase,J,Bool.false_eq_true,ite_false,ite_true]
  all_goals rw [if_neg a,if_neg b]; exact atD fr j 0 0 W h hh
private theorem sourceEnd {T L n F r} (fr : Banks T L n F r) (W v u c j : Nat) (side loc : Bool) :
    phase T L n F r W side v u c j (source F r n loc+r+1)=none := by
  cases loc
  · rw [show source F r n false+r+1=D F r n 5 by dsimp [source,D]; omega]
    exact phaseD fr W v u c j 5 side (by decide)
  · rw [show source F r n true+r+1=D F r n 4 by dsimp [source,D]; omega]
    exact phaseD fr W v u c j 4 side (by decide)
private theorem sourceCell {T L n F r} (_fr : Banks T L n F r) (W v u c j i : Nat) (side : Bool)
    (lo : source F r n side < i) (hi : i < source F r n side+r+1) :
    phase T L n F r W side v u c j i=some (decide (source F r n side+u < i ∧ i ≤ source F r n side+v)) := by
  cases side <;> simp only [source,phase,J,Bool.false_eq_true,ite_false,ite_true,D] at *
  all_goals split_ifs <;> first | rfl | (exfalso; omega)
private theorem destCell {T L n F r} (_fr : Banks T L n F r) (W v u c j i : Nat) (side : Bool)
    (lo : source F r n (!side) < i) (hi : i < source F r n (!side)+r+1) :
    phase T L n F r W side v u c j i=some (decide (i ≤ source F r n (!side)+c)) := by
  cases side <;> simp only [source,phase,J,Bool.false_eq_true,Bool.not_false,Bool.not_true,ite_false,ite_true,D] at *
  all_goals split_ifs <;> first | rfl | (exfalso; omega) | (apply congrArg some; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem advanceSource {T L n F r} (fr : Banks T L n F r) (W v u c j : Nat) (side : Bool) (space : u < r) :
    put (phase T L n F r W side v u c j) (source F r n side+u+1) (some false)=phase T L n F r W side v (u+1) c j := by
  funext i; have room:=banks_room fr
  cases side <;> simp only [put,phase,J,I,CappedWeight.Target.image,source,D,Bool.false_eq_true,ite_false,ite_true]
  all_goals split_ifs <;> first | rfl | (exfalso; omega) | (apply congrArg some; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem advanceDest {T L n F r} (fr : Banks T L n F r) (W v u c j : Nat) (side : Bool) (space : c < r) :
    put (phase T L n F r W side v u c j) (source F r n (!side)+c+1) (some true)=phase T L n F r W side v u (c+1) j := by
  funext i; have room:=banks_room fr
  cases side <;> simp only [put,phase,J,I,CappedWeight.Target.image,source,D,Bool.false_eq_true,Bool.not_false,Bool.not_true,ite_false,ite_true]
  all_goals split_ifs <;> first | rfl | (exfalso; omega) | (apply congrArg some; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem advanceCount {T L n F r} (fr : Banks T L n F r) (W v u c j : Nat) (side : Bool) (space : j < r) :
    put (phase T L n F r W side v u c j) (D F r n 2+j+1) (some true)=phase T L n F r W side v u c (j+1) := by
  funext i; have room:=banks_room fr
  cases side <;> simp only [put,phase,J,I,CappedWeight.Target.image,D,Bool.false_eq_true,ite_false,ite_true]
  all_goals split_ifs <;> first | rfl | (exfalso; omega) | (apply congrArg some; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem phaseTurn (T : Nat → Option Bool) (L n F r W : Nat) (v c j : Nat) (side : Bool) :
    phase T L n F r W side v v c j=phase T L n F r W (!side) c 0 0 j := by
  cases side <;> funext i <;> simp only [phase,J,Bool.false_eq_true,Bool.not_false,Bool.not_true,ite_false,ite_true]
  all_goals split_ifs <;> first | rfl | omega | (apply congrArg some; exact decide_eq_decide.mpr (by omega))
private theorem phaseOcc {T L n F r} (fr : Banks T L n F r) (W v u c j h i : Nat) (side : Bool)
    (hl : 2 ≤ h) (hu : h < 6) (lo : D F r n h < i) (hi : i < D F r n (h+1)) :
    ∃ b, phase T L n F r W side v u c j i=some b := by
  cases side <;> simp only [phase,J,Bool.false_eq_true,ite_false,ite_true]
  all_goals split_ifs
  all_goals first | exact ⟨_,rfl⟩ | exact ⟨_,atBank fr _ _ _ _ h i hl hu lo hi⟩
private theorem phaseRight {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v u c j s out h : Nat) (side : Bool) (hl : 2 ≤ h) (hu : h < 6)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k (s+1)) (some b)=(Cursor.q k (s+1),some b,.right))
    (exit : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k out,none,.stay)) :
    Path k P (r+2) ⟨Cursor.q k s,D F r n h,phase T L n F r W side v u c j⟩
      ⟨Cursor.q k out,D F r n (h+1),phase T L n F r W side v u c j⟩ := by
  rw [Dstep F r n h hl hu]
  exact crossR s (s+1) out (D F r n h) r _ (by rw [←Dstep F r n h hl hu]; exact Dbound F r n _ P (by omega) fit)
    (phaseD fr _ _ _ _ _ _ side (by omega))
    (by rw [←Dstep F r n h hl hu]; exact phaseD fr _ _ _ _ _ _ side (by omega))
    (by intro i lo hi; exact phaseOcc fr _ _ _ _ _ h i side hl hu lo (by rwa [Dstep F r n h hl hu])) entry body exit
private theorem phaseLeft {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v u c j s out h : Nat) (side : Bool) (hl : 2 ≤ h) (hu : h < 6)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.left))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k (s+1)) (some b)=(Cursor.q k (s+1),some b,.left))
    (exit : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k out,none,.stay)) :
    Path k P (r+2) ⟨Cursor.q k s,D F r n (h+1),phase T L n F r W side v u c j⟩
      ⟨Cursor.q k out,D F r n h,phase T L n F r W side v u c j⟩ := by
  rw [Dstep F r n h hl hu]
  exact crossL s (s+1) out (D F r n h) r _ (by rw [←Dstep F r n h hl hu]; exact Dbound F r n _ P (by omega) fit)
    (phaseD fr _ _ _ _ _ _ side (by omega))
    (by rw [←Dstep F r n h hl hu]; exact phaseD fr _ _ _ _ _ _ side (by omega))
    (by intro i lo hi; exact phaseOcc fr _ _ _ _ _ h i side hl hu lo (by rwa [Dstep F r n h hl hu])) entry body exit
private theorem pairErase {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v c j : Nat) (side first : Bool) (space : 2*c+2 ≤ v) (vr : v ≤ r) :
    Path k P (4*c+5)
      ⟨Cursor.q k (lab side (if first then 482 else 486) (if first then 513 else 518)+93*k),source F r n side,phase T L n F r W side v (2*c) c j⟩
      ⟨Cursor.q k (lab side 490 522+93*k),source F r n side,phase T L n F r W side v (2*c+2) c j⟩ := by
  let h:=source F r n side
  have heq : h=source F r n side := rfl
  let A:=phase T L n F r W side v (2*c) c j
  let B:=phase T L n F r W side v (2*c+1) c j
  let C:=phase T L n F r W side v (2*c+2) c j
  let s:=lab side (if first then 482 else 486) (if first then 513 else 518)+93*k
  let scan:=lab side (if first then 483 else 487) (if first then 514 else 519)+93*k
  have room : h+r+1 ≤ P := by cases side <;> dsimp [h,source,D] at * <;> omega
  have sep : A h=none := by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide)
  have a:=K s scan h (h+1) A none .right (P:=P) (by omega) (by omega) sep
    (by cases side <;> cases first <;> dsimp [s,scan,lab] <;> run_tac rowTac) rfl
  have b:=sweepR (Cursor.q k scan) A (h+1) (2*c) (P:=P) (by omega) (by
    intro i lo hi
    have cell:=sourceCell fr W v (2*c) c j i side (by omega) (by omega)
    rw [show A i=some false by dsimp only [A]; rw [cell,decide_eq_false (by omega)]]
    cases side <;> cases first <;> dsimp [scan,lab] <;> run_tac rowTac)
  rw [show h+1+2*c=h+2*c+1 by omega] at b
  have c1:=hop (P:=P) (Cursor.q k scan) (Cursor.q k (lab side 488 520+93*k)) (h+2*c+1) (h+2*c+2) A (some false) .right
    (by omega) (by omega) (by
      have val:=sourceCell fr W v (2*c) c j (h+2*c+1) side (by omega) (by omega)
      rw [show A (h+2*c+1)=some true by dsimp only [A]; rw [val,decide_eq_true (by omega)]]
      cases side <;> cases first <;> dsimp [scan,lab] <;> run_tac rowTac) rfl
  rw [show h+2*c+1=source F r n side+2*c+1 from rfl,advanceSource fr W v (2*c) c j side (by omega)] at c1
  have c2:=hop (P:=P) (Cursor.q k (lab side 488 520+93*k)) (Cursor.q k (lab side 489 521+93*k)) (h+2*c+2) (h+2*c+1) B (some false) .left
    (by omega) (by omega) (by
      have val:=sourceCell fr W v (2*c+1) c j (h+2*c+2) side (by omega) (by omega)
      rw [show B (h+2*c+2)=some true by dsimp only [B]; rw [val,decide_eq_true (by omega)]]
      cases side <;> dsimp [lab] <;> run_tac rowTac) (by simp [dest])
  rw [show h+2*c+2=source F r n side+(2*c+1)+1 by omega,advanceSource fr W v (2*c+1) c j side (by omega)] at c2
  have rev:=sweepL (Cursor.q k (lab side 489 521+93*k)) C h (2*c+1) (P:=P) (by omega) (by
    intro i lo hi
    have val:=sourceCell fr W v (2*c+2) c j i side (by omega) (by omega)
    rw [show C i=some false by dsimp only [C]; rw [val,decide_eq_false (by omega)]]
    cases side <;> dsimp [lab] <;> run_tac rowTac)
  have done:=K (lab side 489 521+93*k) (lab side 490 522+93*k) h h C none .stay (P:=P) (by omega) (by omega)
    (by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide))
    (by cases side <;> dsimp [lab] <;> run_tac rowTac) rfl
  convert a.append b |>.append c1 |>.append c2 |>.append rev |>.append done using 1
  all_goals omega

private theorem destAdd {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v u c j : Nat) (side : Bool) (room : c < r) :
    Path k P (2*c+3) ⟨Cursor.q k (lab side 492 524+93*k),source F r n (!side),phase T L n F r W side v u c j⟩
      ⟨Cursor.q k (lab side 496 528+93*k),source F r n (!side),phase T L n F r W side v u (c+1) j⟩ := by
  have a:=inc (P:=P) (lab side 492 524+93*k) (lab side 496 528+93*k) (lab side 509 541+93*k)
    (source F r n (!side)) r c (phase T L n F r W side v u c j)
    (by cases side <;> dsimp [source,D] at * <;> omega) (by omega)
    (by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide))
    (sourceEnd fr W v u c j side (!side))
    (by intro i lo hi; exact destCell fr W v u c j i side lo hi)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by intro b; cases side <;> cases b <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
  simp only [if_pos room] at a
  rw [advanceDest fr W v u c j side room] at a
  exact a
private theorem pairStep {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v c j : Nat) (side first : Bool) (space : 2*c+2 ≤ v) (vr : v ≤ r) :
    Path k P (6*c+2*r+12)
      ⟨Cursor.q k (lab side (if first then 482 else 486) (if first then 513 else 518)+93*k),source F r n side,phase T L n F r W side v (2*c) c j⟩
      ⟨Cursor.q k (lab side 486 518+93*k),source F r n side,phase T L n F r W side v (2*(c+1)) (c+1) j⟩ := by
  have a:=pairErase (k:=k) fr fit W v c j side first space vr
  have b : Path k P (r+2)
      ⟨Cursor.q k (lab side 490 522+93*k),source F r n side,phase T L n F r W side v (2*c+2) c j⟩
      ⟨Cursor.q k (lab side 492 524+93*k),source F r n (!side),phase T L n F r W side v (2*c+2) c j⟩ := by
    cases side
    · exact phaseLeft fr fit W v (2*c+2) c j (490+93*k) (492+93*k) 3 false (by decide) (by decide)
        (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    · exact phaseRight fr fit W v (2*c+2) c j (522+93*k) (524+93*k) 3 true (by decide) (by decide)
        (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  have c':=destAdd (k:=k) fr fit W v (2*c+2) c j side (by omega)
  have d : Path k P (r+2)
      ⟨Cursor.q k (lab side 496 528+93*k),source F r n (!side),phase T L n F r W side v (2*c+2) (c+1) j⟩
      ⟨Cursor.q k (lab side 486 518+93*k),source F r n side,phase T L n F r W side v (2*c+2) (c+1) j⟩ := by
    cases side
    · exact phaseRight fr fit W v (2*c+2) (c+1) j (496+93*k) (486+93*k) 3 false (by decide) (by decide)
        (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    · exact phaseLeft fr fit W v (2*c+2) (c+1) j (528+93*k) (518+93*k) 3 true (by decide) (by decide)
        (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  convert a.append b |>.append c' |>.append d using 1
  all_goals omega
private theorem pairMany {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v c d j : Nat) (side : Bool) (space : 2*(c+d) ≤ v) (vr : v ≤ r) :
    ∃ t, t ≤ 32*d*(P+1) ∧ Path k P t
      ⟨Cursor.q k (lab side 486 518+93*k),source F r n side,phase T L n F r W side v (2*c) c j⟩
      ⟨Cursor.q k (lab side 486 518+93*k),source F r n side,phase T L n F r W side v (2*(c+d)) (c+d) j⟩ := by
  induction d generalizing c with
  | zero =>
    exact ⟨0,by omega,by simpa using Path.nil ⟨Cursor.q k (lab side 486 518+93*k),source F r n side,phase T L n F r W side v (2*c) c j⟩ (by change source F r n side ≤ P; cases side <;> dsimp [source,D] at * <;> omega)⟩
  | succ d ih =>
    have a:=pairStep (k:=k) fr fit W v c j side false (by omega) vr
    obtain ⟨t,ht,b⟩:=ih (c+1) (by omega)
    rw [show c+1+d=c+(d+1) by omega] at b
    refine ⟨_,?_,a.append b⟩
    have bound : r ≤ P := by dsimp [D] at fit; omega
    nlinarith only [ht,space,vr,bound,Nat.zero_le c,Nat.zero_le d]
private theorem finishEven {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side first : Bool) (_vp : 0 < v) (_vr : v ≤ r) (even : 2*(v/2)=v) (nf : first=false) :
    ∃ t, t ≤ 4*r+4 ∧ Path k P t
      ⟨Cursor.q k (lab side (if first then 483 else 487) (if first then 514 else 519)+93*k),source F r n side+1,phase T L n F r W side v (2*(v/2)) (v/2) j⟩
      ⟨Cursor.q k (lab side 499 531+93*k),source F r n side,phase T L n F r W side v v (v/2) j⟩ := by
  subst first
  let h:=source F r n side; let c:=v/2
  let seek:=lab side (if false then 483 else 487) (if false then 514 else 519)+93*k
  let T0:=phase T L n F r W side v (2*c) c j
  let E:=phase T L n F r W side v v c j
  have heq : h=source F r n side := rfl
  have hf : h+r+1 ≤ P := by cases side <;> dsimp [h,source,D] at * <;> omega
  have ed : E h=none := by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide)
  have endD : E (h+r+1)=none := sourceEnd fr W v v c j side side
  have same : T0=E := by dsimp only [T0,E]; rw [even]
  change ∃ t, t ≤ 4*r+4 ∧ Path k P t ⟨Cursor.q k seek,h+1,T0⟩ ⟨Cursor.q k (lab side 499 531+93*k),h,E⟩
  rw [same]
  have b:=sweepR (Cursor.q k seek) E (h+1) r (P:=P) (by omega) (by
    intro i lo hi; have val:=sourceCell fr W v v c j i side (by omega) (by omega)
    rw [show E i=some false by dsimp only [E]; rw [val,decide_eq_false (by omega)]]
    cases side <;> dsimp [seek,lab] <;> run_tac rowTac)
  rw [show h+1+r=h+r+1 by omega] at b
  have d:=K seek (lab side 498 530+93*k) (h+r+1) (h+r) E none .left (P:=P) (by omega) (by omega) endD
    (by cases side <;> dsimp [seek,lab] <;> run_tac rowTac) (by simp [dest])
  have e:=sweepL (Cursor.q k (lab side 498 530+93*k)) E h r (P:=P) (by omega) (by
    intro i lo hi; have val:=sourceCell fr W v v c j i side (by omega) (by omega)
    rw [show E i=some false by dsimp only [E]; rw [val,decide_eq_false (by omega)]]
    cases side <;> dsimp [lab] <;> run_tac rowTac)
  have f:=K (lab side 498 530+93*k) (lab side 499 531+93*k) h h E none .stay (P:=P) (by omega) (by omega) ed
    (by cases side <;> dsimp [lab] <;> run_tac rowTac) rfl
  exact ⟨_,by omega,b.append d |>.append e |>.append f⟩
private theorem finishOdd {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side first : Bool) (vp : 0 < v) (vr : v ≤ r) (odd : 2*(v/2)+1=v) :
    ∃ t, t ≤ 4*r+4 ∧ Path k P t
      ⟨Cursor.q k (lab side (if first then 483 else 487) (if first then 514 else 519)+93*k),source F r n side+1,phase T L n F r W side v (2*(v/2)) (v/2) j⟩
      ⟨Cursor.q k (lab side 499 531+93*k),source F r n side,phase T L n F r W side v v (v/2) j⟩ := by
  let h:=source F r n side; let c:=v/2
  let seek:=lab side (if first then 483 else 487) (if first then 514 else 519)+93*k
  let T0:=phase T L n F r W side v (2*c) c j
  let E:=phase T L n F r W side v v c j
  have heq : h=source F r n side := rfl
  have hf : h+r+1 ≤ P := by cases side <;> dsimp [h,source,D] at * <;> omega
  have ed : E h=none := by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide)
  have endD : E (h+r+1)=none := sourceEnd fr W v v c j side side
  have b:=sweepR (Cursor.q k seek) T0 (h+1) (2*c) (P:=P) (by omega) (by
    intro i lo hi; have val:=sourceCell fr W v (2*c) c j i side (by omega) (by omega)
    rw [show T0 i=some false by dsimp only [T0]; rw [val,decide_eq_false (by omega)]]
    cases side <;> cases first <;> dsimp [seek,lab] <;> run_tac rowTac)
  rw [show h+1+2*c=h+v by omega] at b
  have val : T0 (h+v)=some true := by
    have hc:=sourceCell fr W v (2*c) c j (h+v) side (by omega) (by omega)
    dsimp only [T0]; rw [hc,decide_eq_true (by omega)]
  have d:=hop (P:=P) (Cursor.q k seek) (Cursor.q k (lab side 488 520+93*k)) (h+v) (h+v+1) T0 (some false) .right
    (by omega) (by omega) (by rw [val]; cases side <;> cases first <;> dsimp [seek,lab] <;> run_tac rowTac) rfl
  have same : put T0 (h+v) (some false)=E := by
    have up:=advanceSource fr W v (2*c) c j side (by omega)
    have eqc : 2*c+1=v := odd
    rw [show source F r n side+2*c+1=h+v by omega,eqc] at up
    exact up
  rw [same] at d
  have e:=K (lab side 488 520+93*k) (lab side 498 530+93*k) (h+v+1) (h+v) E (E (h+v+1)) .left
    (P:=P) (by omega) (by omega) rfl (by
      by_cases full : v=r
      · rw [full,endD]; cases side <;> dsimp [lab] <;> run_tac rowTac
      · have hc:=sourceCell fr W v v c j (h+v+1) side (by omega) (by omega)
        rw [show E (h+v+1)=some false by dsimp only [E]; rw [hc,decide_eq_false (by omega)]]
        cases side <;> dsimp [lab] <;> run_tac rowTac) (by simp [dest])
  have f:=sweepL (Cursor.q k (lab side 498 530+93*k)) E h v (P:=P) (by omega) (by
    intro i lo hi; have hc:=sourceCell fr W v v c j i side (by omega) (by omega)
    rw [show E i=some false by dsimp only [E]; rw [hc,decide_eq_false (by omega)]]
    cases side <;> dsimp [lab] <;> run_tac rowTac)
  have g:=K (lab side 498 530+93*k) (lab side 499 531+93*k) h h E none .stay (P:=P) (by omega) (by omega) ed
    (by cases side <;> dsimp [lab] <;> run_tac rowTac) rfl
  exact ⟨_,by omega,b.append d |>.append e |>.append f |>.append g⟩
private theorem finishHalf {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side first : Bool) (vp : 0 < v) (vr : v ≤ r) (ff : first=true → v/2=0) :
    ∃ t, t ≤ 4*(r+1)+2 ∧ Path k P t
      ⟨Cursor.q k (lab side (if first then 482 else 486) (if first then 513 else 518)+93*k),source F r n side,phase T L n F r W side v (2*(v/2)) (v/2) j⟩
      ⟨Cursor.q k (lab side 499 531+93*k),source F r n side,phase T L n F r W side v v (v/2) j⟩ := by
  let h:=source F r n side; let c:=v/2
  have heq : h=source F r n side := rfl
  let start:=lab side (if first then 482 else 486) (if first then 513 else 518)+93*k
  let seek:=lab side (if first then 483 else 487) (if first then 514 else 519)+93*k
  let T0:=phase T L n F r W side v (2*c) c j
  let E:=phase T L n F r W side v v c j
  have hf : h+r+1 ≤ P := by cases side <;> dsimp [h,source,D] at * <;> omega
  have sep : T0 h=none := by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide)
  have ed : E h=none := by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide)
  have endD : E (h+r+1)=none := by exact sourceEnd fr W v v c j side side
  have a:=K start seek h (h+1) T0 none .right (P:=P) (by omega) (by omega) sep
    (by cases side <;> cases first <;> dsimp [start,seek,lab] <;> run_tac rowTac) rfl
  obtain ⟨t,ht,rest⟩ : ∃ t, t ≤ 4*r+4 ∧ Path k P t ⟨Cursor.q k seek,h+1,T0⟩ ⟨Cursor.q k (lab side 499 531+93*k),h,E⟩ := by
    by_cases even : 2*c=v
    · have nf : first=false := by
        cases first
        · rfl
        · have hh:=ff rfl; dsimp only [c] at even; omega
      exact finishEven (k:=k) fr fit W v j side first vp vr even nf
    · exact finishOdd (k:=k) fr fit W v j side first vp vr (by dsimp only [c] at *; omega)
  exact ⟨_,by omega,a.append rest⟩
private theorem counterCell {T L n F r} (fr : Banks T L n F r) (W v u c j i : Nat) (side : Bool)
    (lo : D F r n 2 < i) (hi : i < D F r n 3) :
    phase T L n F r W side v u c j i=some (decide (i ≤ D F r n 2+j)) := by
  have eq : phase T L n F r W side v u c j i=I T L n F r j 0 0 W i := by
    cases side <;> simp only [phase,Bool.false_eq_true,ite_false,ite_true]
    all_goals dsimp only [J]
    all_goals rw [if_neg (by dsimp [D] at lo hi ⊢; omega),if_neg (by dsimp [D] at lo hi ⊢; omega)]
  rw [eq]; exact atBank fr j 0 0 W 2 i (by decide) (by decide) lo hi
private theorem countAdd {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v c j : Nat) (side : Bool) (room : j < r) :
    Path k P (2*j+3) ⟨Cursor.q k (lab side 503 533+93*k),D F r n 2,phase T L n F r W side v v c j⟩
      ⟨Cursor.q k (lab side 507 537+93*k),D F r n 2,phase T L n F r W side v v c (j+1)⟩ := by
  have a:=inc (P:=P) (lab side 503 533+93*k) (lab side 507 537+93*k) (lab side 509 541+93*k)
    (D F r n 2) r j (phase T L n F r W side v v c j)
    (by dsimp [D] at *; omega) (by omega)
    (phaseD fr _ _ _ _ _ _ side (by decide))
    (by rw [←Dstep F r n 2 (by decide) (by decide)]; exact phaseD fr _ _ _ _ _ _ side (by decide))
    (by intro i lo hi; exact counterCell fr W v v c j i side lo (by rwa [Dstep F r n 2 (by decide) (by decide)]))
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by intro b; cases side <;> cases b <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
    (by cases side <;> dsimp [lab] <;> run_tac rowTac)
  simp only [if_pos room] at a
  rw [advanceCount fr W v v c j side room] at a
  exact a
private theorem halfPass {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side : Bool) (vp : 0 < v) (vr : v ≤ r) :
     ∃ t, t ≤ 64*(v+1)*(P+1) ∧ Path k P t
      ⟨Cursor.q k (lab side 482 513+93*k),source F r n side,phase T L n F r W side v 0 0 j⟩
      ⟨Cursor.q k (lab side 499 531+93*k),source F r n side,phase T L n F r W side v v (v/2) j⟩ := by
  have rP : r ≤ P := by dsimp [D] at fit; omega
  by_cases small : v/2=0
  · obtain ⟨t,ht,h⟩:=finishHalf (k:=k) fr fit W v j side true vp vr (by intro _; exact small)
    refine ⟨t,by nlinarith only [ht,rP,Nat.zero_le v],?_⟩
    simpa only [small,Nat.mul_zero] using h
  · have a:=pairStep (k:=k) fr fit W v 0 j side true (by omega) vr
    obtain ⟨u,hu,b⟩:=pairMany (k:=k) fr fit W v 1 (v/2-1) j side (by omega) vr
    rw [show 1+(v/2-1)=v/2 by omega] at b
    obtain ⟨w,hw,c⟩:=finishHalf (k:=k) fr fit W v j side false vp vr (by intro h; cases h)
    refine ⟨_,?_,a.append b |>.append c⟩
    have ub : u ≤ 32*v*(P+1) := hu.trans (Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_left 32 (by omega)))
    nlinarith only [ub,hw,rP,vr,Nat.zero_le (P*v)]
private theorem toCounter {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side : Bool) : ∃ u, u ≤ 2*r+4 ∧ Path k P u
      ⟨Cursor.q k (lab side 499 531+93*k),source F r n side,phase T L n F r W side v v (v/2) j⟩
      ⟨Cursor.q k (lab side 503 533+93*k),D F r n 2,phase T L n F r W side v v (v/2) j⟩ := by
  cases side
  · have a:=phaseLeft (k:=k) fr fit W v v (v/2) j (499+93*k) (501+93*k) 3 false (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    have b:=phaseLeft (k:=k) fr fit W v v (v/2) j (501+93*k) (503+93*k) 2 false (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    exact ⟨_,by omega,a.append b⟩
  · exact ⟨r+2,by omega,phaseLeft (k:=k) fr fit W v v (v/2) j (531+93*k) (533+93*k) 2 true (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)⟩
private theorem fromCounter {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side : Bool) : ∃ w, w ≤ 2*r+4 ∧ Path k P w
      ⟨Cursor.q k (lab side 507 537+93*k),D F r n 2,phase T L n F r W side v v (v/2) (j+1)⟩
      ⟨Cursor.q k (lab (!side) 482 513+93*k),source F r n (!side),phase T L n F r W side v v (v/2) (j+1)⟩ := by
  cases side
  · exact ⟨r+2,by omega,phaseRight (k:=k) fr fit W v v (v/2) (j+1) (507+93*k) (513+93*k) 2 false (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)⟩
  · have a:=phaseRight (k:=k) fr fit W v v (v/2) (j+1) (537+93*k) (539+93*k) 2 true (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    have b:=phaseRight (k:=k) fr fit W v v (v/2) (j+1) (539+93*k) (482+93*k) 3 true (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    exact ⟨_,by omega,a.append b⟩
private theorem halfCycle {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side : Bool) (vp : 0 < v) (vr : v ≤ r) (jr : j < r) :
    ∃ t, t ≤ 512*(P+1)^2 ∧ Path k P t
      ⟨Cursor.q k (lab side 482 513+93*k),source F r n side,phase T L n F r W side v 0 0 j⟩
      ⟨Cursor.q k (lab (!side) 482 513+93*k),source F r n (!side),phase T L n F r W (!side) (v/2) 0 0 (j+1)⟩ := by
  have rP : r ≤ P := by dsimp [D] at fit; omega
  obtain ⟨t,ht,h⟩:=halfPass (k:=k) fr fit W v j side vp vr
  obtain ⟨u,hu,a⟩:=toCounter (k:=k) fr fit W v j side
  have b:=countAdd (k:=k) fr fit W v (v/2) j side jr
  obtain ⟨w,hw,c⟩:=fromCounter (k:=k) fr fit W v j side
  have joined:=h.append a |>.append b |>.append c
  rw [phaseTurn] at joined
  refine ⟨_,?_,joined⟩
  nlinarith only [ht,hu,hw,rP,vr,jr,Nat.zero_le (P*P)]
private theorem zeroPhase {T L n F r} (fr : Banks T L n F r) (W j : Nat) (side : Bool) :
    phase T L n F r W side 0 0 0 j=I T L n F r j 0 0 W := by
  funext i; have room:=banks_room fr
  cases side <;> simp only [phase,Bool.false_eq_true,ite_false,ite_true]
  all_goals dsimp only [J,I,CappedWeight.Target.image,D]
  all_goals split_ifs <;> first | rfl | (exfalso; omega) | (apply congrArg some; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem initialPhase {T L n F r} (fr : Banks T L n F r) (W : Nat) :
    phase T L n F r W false W 0 0 0=I T L n F r 0 0 W W := by
  funext i; have room:=banks_room fr
  simp only [phase,Bool.false_eq_true,ite_false]
  dsimp only [J,I,CappedWeight.Target.image,D]
  split_ifs <;> first | rfl | (exfalso; omega) | (apply congrArg some; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem emptyLength {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W j : Nat) (side : Bool) :
    ∃ t, t ≤ 8*(P+1) ∧ Path k P t
      ⟨Cursor.q k (lab side 482 513+93*k),source F r n side,phase T L n F r W side 0 0 0 j⟩
      ⟨Cursor.q k (545+93*k),D F r n 4,I T L n F r j 0 0 W⟩ := by
  let T0:=phase T L n F r W side 0 0 0 j
  let h:=source F r n side
  have heq : h=source F r n side := rfl
  have hf : h+r+1 ≤ P := by cases side <;> dsimp [h,source,D] at * <;> omega
  have sep : T0 h=none := by cases side <;> exact phaseD fr _ _ _ _ _ _ _ (by decide)
  have ed : T0 (h+r+1)=none := by exact sourceEnd fr W 0 0 0 j side side
  have a:=K (lab side 482 513+93*k) (lab side 483 514+93*k) h (h+1) T0 none .right
    (P:=P) (by omega) (by omega) sep (by cases side <;> dsimp [lab] <;> run_tac rowTac) rfl
  have b:=sweepR (Cursor.q k (lab side 483 514+93*k)) T0 (h+1) r (P:=P) (by omega) (by
    intro i lo hi; have val:=sourceCell fr W 0 0 0 j i side (by omega) (by omega)
    rw [show T0 i=some false by dsimp only [T0]; rw [val,decide_eq_false (by omega)]]
    cases side <;> dsimp [lab] <;> run_tac rowTac)
  rw [show h+1+r=h+r+1 by omega] at b
  have c:=K (lab side 483 514+93*k) (lab side 484 515+93*k) (h+r+1) (h+r) T0 none .left
    (P:=P) (by omega) (by omega) ed (by cases side <;> dsimp [lab] <;> run_tac rowTac) (by simp [dest])
  have d:=sweepL (Cursor.q k (lab side 484 515+93*k)) T0 h r (P:=P) (by omega) (by
    intro i lo hi; have val:=sourceCell fr W 0 0 0 j i side (by omega) (by omega)
    rw [show T0 i=some false by dsimp only [T0]; rw [val,decide_eq_false (by omega)]]
    cases side <;> dsimp [lab] <;> run_tac rowTac)
  have e:=K (lab side 484 515+93*k) (lab side 485 516+93*k) h h T0 none .stay
    (P:=P) (by omega) (by omega) sep (by cases side <;> dsimp [lab] <;> run_tac rowTac) rfl
  have final : ∃ t, t ≤ r+2 ∧ Path k P t ⟨Cursor.q k (lab side 485 516+93*k),h,T0⟩ ⟨Cursor.q k (545+93*k),D F r n 4,T0⟩ := by
    cases side
    · exact ⟨1,by omega,K (485+93*k) (545+93*k) _ _ T0 none .stay (P:=P)
        (by omega) (Dbound F r n 4 P (by decide) fit) sep (by run_tac rowTac) rfl⟩
    · exact ⟨r+2,by omega,phaseRight (k:=k) fr fit W 0 0 0 j (516+93*k) (545+93*k) 3 true (by decide) (by decide)
        (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)⟩
  obtain ⟨t,ht,g⟩:=final
  have rP : r ≤ P := by dsimp [D] at fit; omega
  refine ⟨_,?_,by simpa only [T0,zeroPhase fr] using a.append b |>.append c |>.append d |>.append e |>.append g⟩
  omega
private theorem lengthStep (v : Nat) (vp : 0 < v) : bitLength v=bitLength (v/2)+1 := by
  fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "length_step" => exact OLD v vp
private theorem lengthLoop {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (W v j : Nat) (side : Bool) (vr : v ≤ r) (cap : j+bitLength v ≤ r) :
    ∃ t, t ≤ 1024*(v+1)*(P+1)^2 ∧ Path k P t
      ⟨Cursor.q k (lab side 482 513+93*k),source F r n side,phase T L n F r W side v 0 0 j⟩
      ⟨Cursor.q k (545+93*k),D F r n 4,I T L n F r (j+bitLength v) 0 0 W⟩ := by
  induction v using Nat.strong_induction_on generalizing j side with
  | h v ih =>
    by_cases zero : v=0
    · subst v
      obtain ⟨t,ht,h⟩:=emptyLength (k:=k) fr fit W j side
      exact ⟨t,by nlinarith only [ht,Nat.zero_le (P*P)],by simpa [bitLength] using h⟩
    · have vp : 0 < v := by omega
      have ell:=lengthStep v vp
      have jr : j < r := by omega
      obtain ⟨t,ht,a⟩:=halfCycle (k:=k) fr fit W v j side vp vr jr
      obtain ⟨u,hu,b⟩:=ih (v/2) (by omega) (j+1) (!side) (by omega) (by omega)
      rw [show j+1+bitLength (v/2)=j+bitLength v by omega] at b
      refine ⟨t+u,?_,a.append b⟩
      have q : v/2+1 ≤ v := by omega
      have nonneg : 0 ≤ (P+1)^2 := Nat.zero_le _
      nlinarith only [ht,hu,Nat.mul_le_mul_right ((P+1)^2) q,nonneg,Nat.zero_le v]
private theorem postLength {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (g W : Nat) (wr : W ≤ r) (ellr : bitLength W ≤ r) :
    ∃ t, t ≤ 2048*(W+1)*(P+1)^2 ∧ Path k P t
      ⟨Cursor.q k (430+93*k),D F r n 2,I T L n F r 0 g W 0⟩
      ⟨Cursor.q k (545+93*k),D F r n 4,I T L n F r (bitLength W) 0 0 W⟩ := by
  obtain ⟨t,ht,a⟩:=preparation (k:=k) fr fit g W wr
  obtain ⟨u,hu,b⟩:=lengthLoop (k:=k) fr fit W W 0 false wr (by simpa using ellr)
  rw [initialPhase fr] at b
  simp only [Nat.zero_add] at b
  refine ⟨t+u,?_,a.append b⟩
  nlinarith only [ht,hu,Nat.zero_le (P*P*W),Nat.zero_le (P*P),Nat.zero_le (P*W)]

private theorem seekStart {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (j W : Nat)
    (b0 : ∀ i, D F r n 0 < i → i < D F r n 1 → ∃ b, T i=some b)
    (b1 : ∀ i, D F r n 1 < i → i < D F r n 2 → ∃ b, T i=some b) :
    Path k P (3*r+n+8) ⟨Cursor.q k (545+93*k),D F r n 4,I T L n F r j 0 0 W⟩
      ⟨Cursor.q k (613+93*k),D F r n 0,I T L n F r j 0 0 W⟩ := by
  have a:=leftI (k:=k) fr fit (545+93*k) (547+93*k) j 0 0 W 3 (by decide) (by decide)
    (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  have b:=leftI (k:=k) fr fit (547+93*k) (549+93*k) j 0 0 W 2 (by decide) (by decide)
    (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  have old (i : Nat) (lo : F < i) (hi : i ≤ D F r n 2) : I T L n F r j 0 0 W i=T i := by
    have room:=banks_room fr
    dsimp only [I,CappedWeight.Target.image,D] at hi ⊢
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have c:=crossL (549+93*k) (550+93*k) (551+93*k) (D F r n 1) n (I T L n F r j 0 0 W)
    (P:=P) (by dsimp [D] at *; omega)
    (atD fr _ _ _ _ 1 (by decide))
    (by rw [show D F r n 1+n+1=D F r n 2 by dsimp [D]; omega]; exact atD fr j 0 0 W 2 (by decide))
    (by intro i lo hi; rw [old i (by dsimp [D] at lo; omega) (by dsimp [D] at hi ⊢; omega)]; exact b1 i lo (by dsimp [D] at hi ⊢; omega))
    (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  have d:=crossL (551+93*k) (552+93*k) (613+93*k) (D F r n 0) r (I T L n F r j 0 0 W)
    (P:=P) (by dsimp [D] at *; omega)
    (atD fr _ _ _ _ 0 (by decide))
    (by rw [show D F r n 0+r+1=D F r n 1 by dsimp [D]; omega]; exact atD fr j 0 0 W 1 (by decide))
    (by intro i lo hi; rw [old i (by dsimp [D] at lo; omega) (by dsimp [D] at hi ⊢; omega)]; exact b0 i lo (by dsimp [D] at hi ⊢; omega))
    (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  have eq1 : D F r n 1+n+1=D F r n 2 := by dsimp [D]; omega
  have eq0 : D F r n 0+r+1=D F r n 1 := by dsimp [D]; omega
  rw [eq1] at c
  rw [eq0] at d
  convert a.append b |>.append c |>.append d using 1
  all_goals omega
end PostWeight
