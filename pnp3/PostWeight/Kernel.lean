import PostWeight.Join
namespace PostWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private def rowTac : TacticM Unit := by
  fromDonor "PostWeight.Rows" "PostWeight" "rowTac" => exact (id OLD)
run_cmd do
  let ns := (← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
    n.toString.startsWith "_private.PostWeight.Rows." && n.toString.endsWith ".PostWeight.rowTac"
  unless ns.length=1 && ns.head!.toString=="_private.PostWeight.Rows.0.PostWeight.rowTac" do
    throwError "Ambiguous checked row tactic"
  logInfo m!"private-term|{ns.head!}"
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
private abbrev OldNode (k : Nat) : Type := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Node" => exact OLD k
private def oldNode {k : Nat} (c : Node k) : OldNode k := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Node.mk" => exact OLD c.state c.head c.tape
private abbrev Path (k P t : Nat) (c d : Node k) : Prop := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Path" => exact OLD k P t (oldNode c) (oldNode d)
namespace Path
private theorem nil {k P : Nat} (c : Node k) (hp : c.head ≤ P) : Path k P 0 c c := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Path.nil" => exact OLD (oldNode c) hp
private theorem bounds {k P t c d} (h : Path k P t c d) : c.head ≤ P ∧ d.head ≤ P := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Path.bounds" => exact OLD h
private theorem append {k P t u c d e} (h : Path k P t c d) (g : Path k P u d e) : Path k P (t+u) c e := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Path.append" => exact OLD h g
private theorem execute {k N B P t c d} (h : Path k P t c d) (hp : P < tapeLength N B) :
    (Cursor.machine k).run t (embed c (lt_of_le_of_lt h.bounds.1 hp))=embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "Path.execute" => exact OLD h hp
end Path
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "hop" => exact OLD s s' h h' T b m hb ha row hm
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "keep" => exact OLD s s' h h' T m hb ha row hm
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (fit : h+r ≤ P) (rows : ∀ i, h ≤ i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "sweepR" => exact OLD s T h r fit rows
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (fit : low+r ≤ P) (rows : ∀ i, low < i → i ≤ low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "sweepL" => exact OLD s T low r fit rows
private theorem K {k P : Nat} (s d h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (mv : Move)
    (hb : h ≤ P) (ha : h' ≤ P) (cell : T h=b)
    (row : (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k d,b,mv)) (hm : dest h mv=h') :
    Path k P 1 ⟨Cursor.q k s,h,T⟩ ⟨Cursor.q k d,h',T⟩ :=
  keep _ _ h h' T mv hb ha (by rw [cell]; exact row) hm
private theorem inc {k P : Nat} (s yes no base w v : Nat) (T : Nat → Option Bool)
    (fit : base+w+1 ≤ P) (hv : v ≤ w) (sep : T base=none) (endD : T (base+w+1)=none)
    (unary : ∀ i, base < i → i < base+w+1 → T i=some (decide (i ≤ base+v)))
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
  have first := K (k:=k) s (s+1) base (base+1) T none .right (P:=P) (by omega) (by omega) sep entry rfl
  have fwd := sweepR (Cursor.q k (s+1)) T (base+1) v
     (P:=P) (by omega) (by
      intro i lo hi; have val:=unary i (by omega) (by omega)
      rw [show T i=some true by simpa only [decide_eq_true (by omega : i ≤ base+v)] using val]; exact scan)
  rw [show base+1+v=base+v+1 by omega] at fwd
  by_cases fits : v < w
  · have val : T (base+v+1)=some false := by
      have u:=unary (base+v+1) (by omega) (by omega); simpa only [decide_eq_false (by omega : ¬base+v+1 ≤ base+v)] using u
    have changeTape := hop (P:=P) (Cursor.q k (s+1)) (Cursor.q k (s+2)) (base+v+1) (base+v) T (some true) .left
       (by omega) (by omega) (by rw [val]; exact add) (by simp [dest])
    let U:=put T (base+v+1) (some true)
    have rev:=sweepL (Cursor.q k (s+2)) U base v
       (P:=P) (by omega) (by
        intro i lo hi
        have eq : U i=T i := by dsimp [U,put]; rw [if_neg (by omega)]
        rw [eq]; have u:=unary i lo (by omega); rw [u]; exact back _)
    have last:=K (k:=k) (s+2) yes base base U none .stay (P:=P) (by omega) (by omega)
      (by dsimp [U,put]; rw [if_neg (by omega)]; exact sep) ok rfl
    simpa only [if_pos fits,show 1+v+1+v+1=2*v+3 by omega] using first.append fwd |>.append changeTape |>.append rev |>.append last
  · have eq : v=w := by omega
    have next : T (base+v+1)=none := by simpa only [eq] using endD
    have turn:=K (k:=k) (s+1) (s+3) (base+v+1) (base+v) T none .left (P:=P) (by omega) (by omega) next full (by simp [dest])
    have rev:=sweepL (Cursor.q k (s+3)) T base v
       (P:=P) (by omega) (by
        intro i lo hi; have u:=unary i lo (by omega); rw [u,decide_eq_true hi]; exact bad)
    have last:=K (k:=k) (s+3) no base base T none .stay (P:=P) (by omega) (by omega) sep over rfl
    simpa only [if_neg fits,show 1+v+1+v+1=2*v+3 by omega] using first.append fwd |>.append turn |>.append rev |>.append last
private theorem dec {k P : Nat} (s yes no base w v : Nat) (T : Nat → Option Bool)
    (fit : base+w+1 ≤ P) (hv : v ≤ w) (sep : T base=none) (endD : T (base+w+1)=none)
    (unary : ∀ i, base < i → i < base+w+1 → T i=some (decide (i ≤ base+v)))
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right))
    (tail : ∀ b, b≠some true → (Cursor.machine k).step (Cursor.q k (s+1)) b=(Cursor.q k (s+2),b,.left))
    (take : (Cursor.machine k).step (Cursor.q k (s+2)) (some true)=(Cursor.q k (s+3),some false,.left))
    (back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+3)) (some b)=(Cursor.q k (s+3),some b,.left))
    (ok : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k yes,none,.stay))
    (empty : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k no,none,.stay)) :
    Path k P (2*v+3) ⟨Cursor.q k s,base,T⟩
      ⟨Cursor.q k (if v=0 then no else yes),base,if v=0 then T else put T (base+v) (some false)⟩ := by
  have first:=K (k:=k) s (s+1) base (base+1) T none .right (P:=P) (by omega) (by omega) sep entry rfl
  have fwd:=sweepR (Cursor.q k (s+1)) T (base+1) v
     (P:=P) (by omega) (by
      intro i lo hi; have u:=unary i (by omega) (by omega)
      rw [u,decide_eq_true (by omega : i ≤ base+v)]; exact scan)
  rw [show base+1+v=base+v+1 by omega] at fwd
  have next : T (base+v+1)≠some true := by
    by_cases full : v=w
    · rw [full,endD]; decide
    · have u:=unary (base+v+1) (by omega) (by omega)
      rw [u,decide_eq_false (by omega : ¬base+v+1 ≤ base+v)]; decide
  have turn:=keep (Cursor.q k (s+1)) (Cursor.q k (s+2)) (base+v+1) (base+v) T .left
     (P:=P) (by omega) (by omega) (tail _ next) (by simp [dest])
  by_cases zero : v=0
  · subst v
    have last:=K (k:=k) (s+2) no base base T none .stay (P:=P) (by omega) (by omega) sep empty rfl
    simpa using first.append fwd |>.append turn |>.append last
  · obtain ⟨a,rfl⟩ : ∃ a, v=a+1 := ⟨v-1,by omega⟩
    have cell : T (base+(a+1))=some true := by
      rw [unary _ (by omega) (by omega),decide_eq_true (by omega)]
    have write:=hop (P:=P) (Cursor.q k (s+2)) (Cursor.q k (s+3)) (base+(a+1)) (base+a) T (some false) .left
       (by omega) (by omega) (by rw [cell]; exact take) (by simp [dest])
    let U:=put T (base+(a+1)) (some false)
    have rev:=sweepL (Cursor.q k (s+3)) U base a
       (P:=P) (by omega) (by
        intro i lo hi
        have eq : U i=T i := by dsimp [U,put]; rw [if_neg (by omega)]
        rw [eq,unary _ lo (by omega)]; exact back _)
    have last:=K (k:=k) (s+3) yes base base U none .stay (P:=P) (by omega) (by omega)
      (by dsimp [U,put]; rw [if_neg (by omega)]; exact sep) ok rfl
    simpa only [if_neg (by omega : a+1≠0),show 1+(a+1)+1+1+a+1=2*(a+1)+3 by omega] using
      first.append fwd |>.append turn |>.append write |>.append rev |>.append last
private theorem crossR {k P : Nat} (s scan out low width : Nat) (T : Nat → Option Bool)
    (fit : low+width+1 ≤ P)
    (d : T low=none) (endD : T (low+width+1)=none)
    (occ : ∀ i, low < i → i < low+width+1 → ∃ b, T i=some b)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k scan,none,.right))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k scan) (some b)=(Cursor.q k scan,some b,.right))
    (exit : (Cursor.machine k).step (Cursor.q k scan) none=(Cursor.q k out,none,.stay)) :
    Path k P (width+2) ⟨Cursor.q k s,low,T⟩ ⟨Cursor.q k out,low+width+1,T⟩ := by
  have a := K (k:=k) s scan low (low+1) T none .right (P:=P) (by omega) (by omega) d entry rfl
  have b := sweepR (Cursor.q k scan) T (low+1) width
     (P:=P) (by omega) (by
      intro i lo hi; obtain ⟨b,hb⟩ := occ i (by omega) (by omega); rw [hb]; exact body b)
  rw [show low+1+width=low+width+1 by omega] at b
  have c := K (k:=k) scan out (low+width+1) (low+width+1) T none .stay (P:=P) (by omega) (by omega) endD exit rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b |>.append c
private theorem crossL {k P : Nat} (s scan out low width : Nat) (T : Nat → Option Bool)
    (fit : low+width+1 ≤ P)
    (d : T low=none) (endD : T (low+width+1)=none)
    (occ : ∀ i, low < i → i < low+width+1 → ∃ b, T i=some b)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k scan,none,.left))
    (body : ∀ b, (Cursor.machine k).step (Cursor.q k scan) (some b)=(Cursor.q k scan,some b,.left))
    (exit : (Cursor.machine k).step (Cursor.q k scan) none=(Cursor.q k out,none,.stay)) :
    Path k P (width+2) ⟨Cursor.q k s,low+width+1,T⟩ ⟨Cursor.q k out,low,T⟩ := by
  have a := K (k:=k) s scan (low+width+1) (low+width) T none .left (P:=P) (by omega) (by omega) endD entry (by simp [dest])
  have b := sweepL (Cursor.q k scan) T low width
     (P:=P) (by omega) (by
      intro i lo hi; obtain ⟨b,hb⟩ := occ i lo (by omega); rw [hb]; exact body b)
  have c := K (k:=k) scan out low low T none .stay (P:=P) (by omega) (by omega) d exit rfl
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b |>.append c
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def I (T : Nat → Option Bool) (L n F r a b c d : Nat) : Nat → Option Bool :=
  CappedWeight.Target.image T L n F r a b c d 0
private structure Banks (T : Nat → Option Bool) (L n F r : Nat) : Prop where
  room : L+n+1 < F
  blank : ∀ j, j ≤ 6 → T (D F r n j)=none
private theorem atD {T L n F r} (fr : Banks T L n F r) (a b c d j : Nat) (hj : j ≤ 6) :
    I T L n F r a b c d (D F r n j)=none := by
  have room:=fr.room
  have eq : I T L n F r a b c d (D F r n j)=T (D F r n j) := by
    interval_cases j <;> simp only [I,CappedWeight.Target.image,D]
    all_goals repeat' first | rfl | (exfalso; omega) | split
  rw [eq]; exact fr.blank j hj
private def val (a b c d j : Nat) := if j=2 then a else if j=3 then b else if j=4 then c else d
private theorem atBank {T L n F r} (fr : Banks T L n F r) (a b c d j i : Nat)
    (hj : 2 ≤ j) (hj' : j < 6) (lo : D F r n j < i) (hi : i < D F r n (j+1)) :
    I T L n F r a b c d i=some (decide (i ≤ D F r n j+val a b c d j)) := by
  have room:=fr.room
  interval_cases j <;> dsimp only [D] at lo hi
  all_goals dsimp only [I,CappedWeight.Target.image,D,val]
  all_goals split_ifs <;> first | rfl | (exfalso; omega)
private theorem set3 {T L n F r} (fr : Banks T L n F r) (a b c d : Nat) (fit : b < r) :
    put (I T L n F r a b c d) (D F r n 3+b+1) (some true)=I T L n F r a (b+1) c d := by
  funext i; have room:=fr.room
  simp only [put,I,CappedWeight.Target.image,D]
  split_ifs <;> first | rfl | (exfalso; omega) |
    (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm |
      (exact decide_eq_decide.mpr (by omega)))
private theorem set4 {T L n F r} (fr : Banks T L n F r) (a b c d : Nat) (fit : c < r) :
    put (I T L n F r a b c d) (D F r n 4+c+1) (some true)=I T L n F r a b (c+1) d := by
  funext i; have room:=fr.room
  simp only [put,I,CappedWeight.Target.image,D]
  split_ifs <;> first | rfl | (exfalso; omega) |
    (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm |
      (exact decide_eq_decide.mpr (by omega)))
private theorem set5 {T L n F r} (fr : Banks T L n F r) (a b c d : Nat) (fit : d < r) :
    put (I T L n F r a b c d) (D F r n 5+d+1) (some true)=I T L n F r a b c (d+1) := by
  funext i; have room:=fr.room
  simp only [put,I,CappedWeight.Target.image,D]
  split_ifs <;> first | rfl | (exfalso; omega) |
    (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm |
      (exact decide_eq_decide.mpr (by omega)))
private theorem unset3 {T L n F r} (fr : Banks T L n F r) (a b c d : Nat) (fit : b < r) :
    put (I T L n F r a (b+1) c d) (D F r n 3+b+1) (some false)=I T L n F r a b c d := by
  funext i; have room:=fr.room
  simp only [put,I,CappedWeight.Target.image,D]
  split_ifs <;> first | rfl | (exfalso; omega) |
    (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm |
      (exact decide_eq_decide.mpr (by omega)))
private theorem unset4 {T L n F r} (fr : Banks T L n F r) (a b c d : Nat) (fit : c < r) :
    put (I T L n F r a b (c+1) d) (D F r n 4+c+1) (some false)=I T L n F r a b c d := by
  funext i; have room:=fr.room
  simp only [put,I,CappedWeight.Target.image,D]
  split_ifs <;> first | rfl | (exfalso; omega) |
    (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm |
      (exact decide_eq_decide.mpr (by omega)))
private def paint (T : Nat → Option Bool) (lo hi : Nat) : Nat → Option Bool :=
  fun i => if lo ≤ i ∧ i < hi then some false else T i
private theorem eraseR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h n : Nat)
    (fit : h+n ≤ P) (cells : ∀ i, h ≤ i → i < h+n → ∃ b, T i=some b)
    (row : ∀ b, (Cursor.machine k).step s (some b)=(s,some false,.right)) :
    Path k P n ⟨s,h,T⟩ ⟨s,h+n,paint T h (h+n)⟩ := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "eraseR" => exact OLD s T h n fit cells row
private theorem clearCross {k P : Nat} (s low w : Nat) (T : Nat → Option Bool)
    (fit : low+w+1 ≤ P) (left : T low=none) (right : T (low+w+1)=none)
    (occ : ∀ i, low < i → i < low+w+1 → ∃ b, T i=some b)
    (r0 : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (r1 : ∀ b, (Cursor.machine k).step (Cursor.q k (s+1)) (some b)=(Cursor.q k (s+1),some false,.right))
    (r2 : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+2),none,.left))
    (r3 : (Cursor.machine k).step (Cursor.q k (s+2)) (some false)=(Cursor.q k (s+2),some false,.left))
    (r4 : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k (s+3),none,.stay))
    (r5 : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k (s+4),none,.right))
    (r6 : (Cursor.machine k).step (Cursor.q k (s+4)) (some false)=(Cursor.q k (s+4),some false,.right))
    (r7 : (Cursor.machine k).step (Cursor.q k (s+4)) none=(Cursor.q k (s+5),none,.stay)) :
    Path k P (3*w+5) ⟨Cursor.q k s,low,T⟩
      ⟨Cursor.q k (s+5),low+w+1,paint T (low+1) (low+w+1)⟩ := by
  let U:=paint T (low+1) (low+w+1)
  have a:=K s (s+1) low (low+1) T none .right (P:=P) (by omega) (by omega) left r0 rfl
  have b:=eraseR (Cursor.q k (s+1)) T (low+1) w (P:=P) (by omega) (by intro i lo hi; exact occ i (by omega) (by omega)) r1
  rw [show low+1+w=low+w+1 by omega] at b
  have ul : U low=none := by dsimp only [U,paint]; rw [if_neg (by omega)]; exact left
  have ur : U (low+w+1)=none := by dsimp only [U,paint]; rw [if_neg (by omega)]; exact right
  have ub (i : Nat) (lo : low < i) (hi : i < low+w+1) : U i=some false := by dsimp only [U,paint]; rw [if_pos (by omega)]
  have c:=K (s+1) (s+2) (low+w+1) (low+w) U none .left (P:=P) (by omega) (by omega) ur r2 (by simp [dest])
  have d:=sweepL (Cursor.q k (s+2)) U low w (P:=P) (by omega) (by intro i lo hi; rw [ub i lo (by omega)]; exact r3)
  have e:=K (s+2) (s+3) low low U none .stay (P:=P) (by omega) (by omega) ul r4 rfl
  have f:=K (s+3) (s+4) low (low+1) U none .right (P:=P) (by omega) (by omega) ul r5 rfl
  have g:=sweepR (Cursor.q k (s+4)) U (low+1) w (P:=P) (by omega) (by intro i lo hi; rw [ub i (by omega) (by omega)]; exact r6)
  rw [show low+1+w=low+w+1 by omega] at g
  have h:=K (s+4) (s+5) (low+w+1) (low+w+1) U none .stay (P:=P) (by omega) (by omega) ur r7 rfl
  convert a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append h using 1
  omega
private theorem Dstep (F r n j : Nat) (lo : 2 ≤ j) (hi : j < 6) : D F r n (j+1)=D F r n j+r+1 := by
  interval_cases j <;> simp only [D] <;> omega
private theorem Dbound (F r n j P : Nat) (hj : j ≤ 6) (fit : D F r n 6 ≤ P) : D F r n j ≤ P := by
  interval_cases j <;> simp only [D] at * <;> omega
private theorem rightI {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (s out a b c d j : Nat) (lo : 2 ≤ j) (hi : j < 6)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right))
    (scan : ∀ v, (Cursor.machine k).step (Cursor.q k (s+1)) (some v)=(Cursor.q k (s+1),some v,.right))
    (exit : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k out,none,.stay)) :
    Path k P (r+2) ⟨Cursor.q k s,D F r n j,I T L n F r a b c d⟩
      ⟨Cursor.q k out,D F r n (j+1),I T L n F r a b c d⟩ := by
  rw [Dstep F r n j lo hi]
  exact crossR s (s+1) out (D F r n j) r _ (by rw [←Dstep F r n j lo hi]; exact Dbound F r n _ P (by omega) fit)
    (atD fr a b c d j (by omega)) (by rw [←Dstep F r n j lo hi]; exact atD fr a b c d _ (by omega))
    (by intro i hl hu; exact ⟨_,atBank fr a b c d j i lo hi hl (by rwa [Dstep F r n j lo hi])⟩) entry scan exit
private theorem leftI {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (s out a b c d j : Nat) (lo : 2 ≤ j) (hi : j < 6)
    (entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.left))
    (scan : ∀ v, (Cursor.machine k).step (Cursor.q k (s+1)) (some v)=(Cursor.q k (s+1),some v,.left))
    (exit : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k out,none,.stay)) :
    Path k P (r+2) ⟨Cursor.q k s,D F r n (j+1),I T L n F r a b c d⟩
      ⟨Cursor.q k out,D F r n j,I T L n F r a b c d⟩ := by
  rw [Dstep F r n j lo hi]
  exact crossL s (s+1) out (D F r n j) r _ (by rw [←Dstep F r n j lo hi]; exact Dbound F r n _ P (by omega) fit)
    (atD fr a b c d j (by omega)) (by rw [←Dstep F r n j lo hi]; exact atD fr a b c d _ (by omega))
    (by intro i hl hu; exact ⟨_,atBank fr a b c d j i lo hi hl (by rwa [Dstep F r n j lo hi])⟩) entry scan exit
private theorem clock_more (P v a b : Nat) (ha : a ≤ 32*(P+1)) (hb : b ≤ 128*(v+1)*(P+1)) :
    a+b ≤ 128*(v+2)*(P+1) := by nlinarith only [ha,hb,Nat.zero_le P]
private structure IncRows (k s yes no : Nat) : Prop where
  entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right)
  scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right)
  add : (Cursor.machine k).step (Cursor.q k (s+1)) (some false)=(Cursor.q k (s+2),some true,.left)
  full : (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+3),none,.left)
  back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+2)) (some b)=(Cursor.q k (s+2),some b,.left)
  ok : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k yes,none,.stay)
  bad : (Cursor.machine k).step (Cursor.q k (s+3)) (some true)=(Cursor.q k (s+3),some true,.left)
  over : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k no,none,.stay)
private structure DecRows (k s yes no : Nat) : Prop where
  entry : (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right)
  scan : (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right)
  tail : ∀ b, b≠some true → (Cursor.machine k).step (Cursor.q k (s+1)) b=(Cursor.q k (s+2),b,.left)
  take : (Cursor.machine k).step (Cursor.q k (s+2)) (some true)=(Cursor.q k (s+3),some false,.left)
  back : ∀ b, (Cursor.machine k).step (Cursor.q k (s+3)) (some b)=(Cursor.q k (s+3),some b,.left)
  ok : (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k yes,none,.stay)
  empty : (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k no,none,.stay)
private theorem inc3_rows (k : Nat) : IncRows k (451+93*k) (455+93*k) (553+93*k) := by
  constructor
  all_goals first | (run_tac rowTac) | (intro b; cases b <;> run_tac rowTac)
private theorem inc4_rows (k : Nat) : IncRows k (465+93*k) (469+93*k) (471+93*k) := by
  constructor
  all_goals first | (run_tac rowTac) | (intro b; cases b <;> run_tac rowTac)
private theorem inc5_rows (k : Nat) : IncRows k (443+93*k) (447+93*k) (553+93*k) := by
  constructor
  all_goals first | (run_tac rowTac) | (intro b; cases b <;> run_tac rowTac)
private theorem dec3_rows (k : Nat) : DecRows k (459+93*k) (463+93*k) (479+93*k) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac rowTac
  · run_tac rowTac
  · intro b hb
    cases b with
    | none => run_tac rowTac
    | some b => cases b with
      | false => run_tac rowTac
      | true => exact False.elim (hb rfl)
  all_goals first | (run_tac rowTac) | (intro b; cases b <;> run_tac rowTac)
private theorem dec4_rows (k : Nat) : DecRows k (437+93*k) (441+93*k) (457+93*k) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · run_tac rowTac
  · run_tac rowTac
  · intro b hb
    cases b with
    | none => run_tac rowTac
    | some b => cases b with
      | false => run_tac rowTac
      | true => exact False.elim (hb rfl)
  all_goals first | (run_tac rowTac) | (intro b; cases b <;> run_tac rowTac)
private theorem add3 {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (a b c d : Nat) (space : b < r) :
    Path k P (2*b+3) ⟨Cursor.q k (451+93*k),D F r n 3,I T L n F r a b c d⟩
      ⟨Cursor.q k (455+93*k),D F r n 3,I T L n F r a (b+1) c d⟩ := by
  have rr:=inc3_rows k
  have step:=inc (P:=P) (451+93*k) (455+93*k) (553+93*k) (D F r n 3) r b (I T L n F r a b c d)
    (by rw [←Dstep F r n 3 (by decide) (by decide)]; exact Dbound F r n _ P (by decide) fit) (by omega)
    (atD fr a b c d 3 (by decide))
    (by rw [←Dstep F r n 3 (by decide) (by decide)]; exact atD fr a b c d _ (by decide))
    (by intro i lo hi; exact atBank fr a b c d 3 i (by decide) (by decide) lo (by rwa [Dstep F r n 3 (by decide) (by decide)]))
    rr.entry rr.scan rr.add rr.full rr.back rr.ok rr.bad rr.over
  simp only [if_pos space] at step
  rw [set3 fr a b c d space] at step
  exact step
private theorem add4 {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (a b c d : Nat) (space : c < r) :
    Path k P (2*c+3) ⟨Cursor.q k (465+93*k),D F r n 4,I T L n F r a b c d⟩
      ⟨Cursor.q k (469+93*k),D F r n 4,I T L n F r a b (c+1) d⟩ := by
  have rr:=inc4_rows k
  have step:=inc (P:=P) (465+93*k) (469+93*k) (471+93*k) (D F r n 4) r c (I T L n F r a b c d)
    (by rw [←Dstep F r n 4 (by decide) (by decide)]; exact Dbound F r n _ P (by decide) fit) (by omega)
    (atD fr a b c d 4 (by decide))
    (by rw [←Dstep F r n 4 (by decide) (by decide)]; exact atD fr a b c d _ (by decide))
    (by intro i lo hi; exact atBank fr a b c d 4 i (by decide) (by decide) lo (by rwa [Dstep F r n 4 (by decide) (by decide)]))
    rr.entry rr.scan rr.add rr.full rr.back rr.ok rr.bad rr.over
  simp only [if_pos space] at step
  rw [set4 fr a b c d space] at step
  exact step
private theorem add5 {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (a b c d : Nat) (space : d < r) :
    Path k P (2*d+3) ⟨Cursor.q k (443+93*k),D F r n 5,I T L n F r a b c d⟩
      ⟨Cursor.q k (447+93*k),D F r n 5,I T L n F r a b c (d+1)⟩ := by
  have rr:=inc5_rows k
  have step:=inc (P:=P) (443+93*k) (447+93*k) (553+93*k) (D F r n 5) r d (I T L n F r a b c d)
    (by rw [←Dstep F r n 5 (by decide) (by decide)]; exact Dbound F r n _ P (by decide) fit) (by omega)
    (atD fr a b c d 5 (by decide))
    (by rw [←Dstep F r n 5 (by decide) (by decide)]; exact atD fr a b c d _ (by decide))
    (by intro i lo hi; exact atBank fr a b c d 5 i (by decide) (by decide) lo (by rwa [Dstep F r n 5 (by decide) (by decide)]))
    rr.entry rr.scan rr.add rr.full rr.back rr.ok rr.bad rr.over
  simp only [if_pos space] at step
  rw [set5 fr a b c d space] at step
  exact step
private theorem take3 {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (a b c d : Nat) (space : b ≤ r) :
    Path k P (2*b+3) ⟨Cursor.q k (459+93*k),D F r n 3,I T L n F r a b c d⟩
      ⟨Cursor.q k (if b=0 then 479+93*k else 463+93*k),D F r n 3,I T L n F r a (b-1) c d⟩ := by
  have rr:=dec3_rows k
  have step:=dec (P:=P) (459+93*k) (463+93*k) (479+93*k) (D F r n 3) r b (I T L n F r a b c d)
    (by rw [←Dstep F r n 3 (by decide) (by decide)]; exact Dbound F r n _ P (by decide) fit) space
    (atD fr a b c d 3 (by decide))
    (by rw [←Dstep F r n 3 (by decide) (by decide)]; exact atD fr a b c d _ (by decide))
    (by intro i lo hi; exact atBank fr a b c d 3 i (by decide) (by decide) lo (by rwa [Dstep F r n 3 (by decide) (by decide)]))
    rr.entry rr.scan rr.tail rr.take rr.back rr.ok rr.empty
  cases b with
  | zero => simpa using step
  | succ v =>
    rw [if_neg (by omega)] at step
    rw [show D F r n 3+(v+1)=D F r n 3+v+1 by omega,unset3 fr _ _ _ _ (by omega)] at step
    simpa using step
private theorem take4 {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (a b c d : Nat) (space : c ≤ r) :
    Path k P (2*c+3) ⟨Cursor.q k (437+93*k),D F r n 4,I T L n F r a b c d⟩
      ⟨Cursor.q k (if c=0 then 457+93*k else 441+93*k),D F r n 4,I T L n F r a b (c-1) d⟩ := by
  have rr:=dec4_rows k
  have step:=dec (P:=P) (437+93*k) (441+93*k) (457+93*k) (D F r n 4) r c (I T L n F r a b c d)
    (by rw [←Dstep F r n 4 (by decide) (by decide)]; exact Dbound F r n _ P (by decide) fit) space
    (atD fr a b c d 4 (by decide))
    (by rw [←Dstep F r n 4 (by decide) (by decide)]; exact atD fr a b c d _ (by decide))
    (by intro i lo hi; exact atBank fr a b c d 4 i (by decide) (by decide) lo (by rwa [Dstep F r n 4 (by decide) (by decide)]))
    rr.entry rr.scan rr.tail rr.take rr.back rr.ok rr.empty
  cases c with
  | zero => simpa using step
  | succ v =>
    rw [if_neg (by omega)] at step
    rw [show D F r n 4+(v+1)=D F r n 4+v+1 by omega,unset4 fr _ _ _ _ (by omega)] at step
    simpa using step
private theorem erase3 {T L n F r} (fr : Banks T L n F r) (a b c d : Nat) :
    paint (I T L n F r a b c d) (D F r n 3+1) (D F r n 4)=I T L n F r a 0 c d := by
  funext i; have room:=fr.room
  simp only [paint,I,CappedWeight.Target.image,D]
  split_ifs <;> first | rfl | (exfalso; omega) |
    (congr 1; exact (decide_eq_false (by omega)).symm)
private theorem copy1 {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (v j : Nat) (room : j+v ≤ r) :
    ∃ t, t ≤ 128*(v+1)*(P+1) ∧ Path k P t
      ⟨Cursor.q k (437+93*k),D F r n 4,I T L n F r 0 j v j⟩
      ⟨Cursor.q k (457+93*k),D F r n 4,I T L n F r 0 (j+v) 0 (j+v)⟩ := by
  have rP : r ≤ P := by dsimp only [D] at fit; omega
  induction v generalizing j with
  | zero =>
    have a:=take4 (k:=k) fr fit 0 j 0 j (by omega)
    exact ⟨3,by omega,by simpa using a⟩
  | succ v ih =>
    have a:=take4 (k:=k) fr fit 0 j (v+1) j (by omega)
    rw [if_neg (by omega)] at a
    have b:=rightI (k:=k) fr fit (441+93*k) (443+93*k) 0 j v j 4 (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    have c:=add5 (k:=k) fr fit 0 j v j (by omega)
    have d:=leftI (k:=k) fr fit (447+93*k) (449+93*k) 0 j v (j+1) 4 (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    have e:=leftI (k:=k) fr fit (449+93*k) (451+93*k) 0 j v (j+1) 3 (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    have f:=add3 (k:=k) fr fit 0 j v (j+1) (by omega)
    have g:=rightI (k:=k) fr fit (455+93*k) (437+93*k) 0 (j+1) v (j+1) 3 (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    obtain ⟨u,hu,rest⟩:=ih (j+1) (by omega)
    rw [show j+1+v=j+(v+1) by omega] at rest
    let price:=2*(v+1)+3+(r+2)+(2*j+3)+(r+2)+(r+2)+(2*j+3)+(r+2)
    refine ⟨price+u,?_,?_⟩
    · exact clock_more P v price u (by dsimp only [price]; omega) hu
    · exact a.append b |>.append c |>.append d |>.append e |>.append f |>.append g |>.append rest
private theorem copy2 {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (v j W : Nat) (room : j+v ≤ r) :
    ∃ t, t ≤ 128*(v+1)*(P+1) ∧ Path k P t
      ⟨Cursor.q k (459+93*k),D F r n 3,I T L n F r 0 v j W⟩
      ⟨Cursor.q k (479+93*k),D F r n 3,I T L n F r 0 0 (j+v) W⟩ := by
  have rP : r ≤ P := by dsimp only [D] at fit; omega
  induction v generalizing j with
  | zero =>
    have a:=take3 (k:=k) fr fit 0 0 j W (by omega)
    exact ⟨3,by omega,by simpa using a⟩
  | succ v ih =>
    have a:=take3 (k:=k) fr fit 0 (v+1) j W (by omega)
    rw [if_neg (by omega)] at a
    have b:=rightI (k:=k) fr fit (463+93*k) (465+93*k) 0 v j W 3 (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    have c:=add4 (k:=k) fr fit 0 v j W (by omega)
    have d:=leftI (k:=k) fr fit (469+93*k) (459+93*k) 0 v (j+1) W 3 (by decide) (by decide)
      (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
    obtain ⟨u,hu,rest⟩:=ih (j+1) (by omega)
    rw [show j+1+v=j+(v+1) by omega] at rest
    let price:=2*(v+1)+3+(r+2)+(2*j+3)+(r+2)
    refine ⟨price+u,?_,?_⟩
    · exact clock_more P v price u (by dsimp only [price]; omega) hu
    · exact a.append b |>.append c |>.append d |>.append rest
private theorem preparation {k P T L n F r} (fr : Banks T L n F r) (fit : D F r n 6 ≤ P)
    (g W : Nat) (room : W ≤ r) :
    ∃ t, t ≤ 512*(W+1)*(P+1) ∧ Path k P t
      ⟨Cursor.q k (430+93*k),D F r n 2,I T L n F r 0 g W 0⟩
      ⟨Cursor.q k (482+93*k),D F r n 4,I T L n F r 0 0 W W⟩ := by
  have a:=rightI (k:=k) fr fit (430+93*k) (432+93*k) 0 g W 0 2 (by decide) (by decide)
    (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  have b:=clearCross (432+93*k) (D F r n 3) r (I T L n F r 0 g W 0) (P:=P)
    (by rw [←Dstep F r n 3 (by decide) (by decide)]; exact Dbound F r n _ P (by decide) fit)
    (atD fr _ _ _ _ _ (by decide))
    (by rw [←Dstep F r n 3 (by decide) (by decide)]; exact atD fr _ _ _ _ _ (by decide))
    (by intro i lo hi; exact ⟨_,atBank fr 0 g W 0 3 i (by decide) (by decide) lo (by rwa [Dstep F r n 3 (by decide) (by decide)])⟩)
    (by run_tac rowTac) (by intro v; cases v <;> run_tac rowTac) (by run_tac rowTac)
    (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
  rw [←Dstep F r n 3 (by decide) (by decide),erase3 fr,show 432+93*k+5=437+93*k by omega] at b
  obtain ⟨u,hu,c⟩:=copy1 (k:=k) fr fit W 0 (by omega)
  simp only [Nat.zero_add] at c
  have d:=leftI (k:=k) fr fit (457+93*k) (459+93*k) 0 W 0 W 3 (by decide) (by decide)
    (by run_tac rowTac) (by intro v; cases v <;> run_tac rowTac) (by run_tac rowTac)
  obtain ⟨v,hv,e⟩:=copy2 (k:=k) fr fit W 0 W (by omega)
  simp only [Nat.zero_add] at e
  have f:=rightI (k:=k) fr fit (479+93*k) (481+93*k) 0 0 W W 3 (by decide) (by decide)
    (by run_tac rowTac) (by intro b; cases b <;> run_tac rowTac) (by run_tac rowTac)
  have g:=K (481+93*k) (482+93*k) (D F r n 4) (D F r n 4) (I T L n F r 0 0 W W) none .stay
    (P:=P) (Dbound F r n 4 P (by decide) fit) (Dbound F r n 4 P (by decide) fit)
    (atD fr _ _ _ _ _ (by decide)) (by run_tac rowTac) rfl
  refine ⟨_,?_,a.append b |>.append c |>.append d |>.append e |>.append f |>.append g⟩
  have rP : r ≤ P := by dsimp only [D] at fit; omega
  nlinarith only [hu,hv,rP,Nat.zero_le (W*P)]
end PostWeight
