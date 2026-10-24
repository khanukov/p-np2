import IngressRepair.Target
namespace IngressRepair
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
set_option linter.unnecessarySeqFocus false
private structure Node (M : UniformTM) where
  state : Fin M.stateCount
  head : Nat
  tape : Nat → Option Bool

private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i

private def embed {M : UniformTM} {N B : Nat} (c : Node M) (h : c.head < tapeLength N B) : Config M.stateCount N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩

private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1

private structure Edge {M : UniformTM} (P : Nat) (c d : Node M) : Prop where
  before : c.head ≤ P
  after : d.head ≤ P
  row : (M.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (M.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (M.step c.state (c.tape c.head)).2.1

private inductive Path {M : UniformTM} (P : Nat) : Nat → Node M → Node M → Prop
  | nil (c) (h : c.head ≤ P) : Path (M := M) P 0 c c
  | cons {t c d e} : Edge (M := M) P c d → Path (M := M) P t d e → Path (M := M) P (t+1) c e

namespace Path
private theorem bounds {M : UniformTM} {P t c d} (h : Path (M := M) P t c d) : c.head ≤ P ∧ d.head ≤ P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩

private theorem append {M : UniformTM} {P t u c d e} (h : Path (M := M) P t c d) (g : Path (M := M) P u d e) :
    Path (M := M) P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)

private theorem execute {M : UniformTM} {N B P t c d} (h : Path (M := M) P t c d) (hp : P < tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge (M := M) P c d) :
      M.stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ (M.step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : (M.step c.state (c.tape c.head)).2.2 with
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
      M.run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; rfl
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,M.run_add]
    change M.run t (M.stepConfig (embed c hc)) = embed e he
    rw [step ed]
    exact ih _ _
end Path

private theorem hop {M : UniformTM} {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool)
    (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : M.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path (M := M) P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha

private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]

/-- One exact public row that preserves the scanned symbol. -/
private theorem keep {M : UniformTM} {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool)
    (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : M.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path (M := M) P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop (M := M) s s' h h' T (T h) m hb ha row hm
  rwa [put_same] at one

private theorem sweepR {M : UniformTM} {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (h r : Nat)
    (fit : h+r ≤ P)
    (rows : ∀ i, h ≤ i → i < h+r → M.step s (T i)=(s,T i,.right)) :
    Path (M := M) P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep (M := M) s s h (h+1) T .right (P := P) (by omega) (by omega)
      (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest

private theorem sweepL {M : UniformTM} {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (low r : Nat)
    (fit : low+r ≤ P)
    (rows : ∀ i, low < i → i ≤ low+r → M.step s (T i)=(s,T i,.left)) :
    Path (M := M) P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep (M := M) s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega)
      (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest

private abbrev O := SmallIngress.producer
private abbrev oq := SmallIngress.q
private theorem gamma_path (T : Nat → Option Bool) (z : Nat)
    (six : T 6=some true) (seven : T 7=some false)
    (zero : ∀ j, j<z → T (8+j)=some false) (term : T (8+z)=some true) :
    Path (M := O) (9+z) (3*z+6) ⟨oq 124,8,T⟩ ⟨oq 133,8+z,put T 7 none⟩ := by
  have p0 := sweepR (M := O) (P := 9+z) (oq 124) T 8 z (by omega) (by
    intro i lo hi
    have h : T i=some false := by convert zero (i-8) (by omega) using 1 <;> congr 1 <;> omega
    rw [h]; decide)
  have p1 := keep (M := O) (P := 9+z) (oq 124) (oq 127) (8+z) (8+z) T .stay
    (by omega) (by omega) (by rw [term]; decide) rfl
  have p2 := keep (M := O) (P := 9+z) (oq 127) (oq 128) (8+z) (7+z) T .left
    (by omega) (by omega) (by rw [term]; decide) (by simp [dest])
  have p3 : Path (M := O) (9+z) (z+1) ⟨oq 128,7+z,T⟩ ⟨oq 128,6,T⟩ := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      sweepL (M := O) (P := 9+z) (oq 128) T 6 (z+1) (by omega) (by
        intro i lo hi
        have h : T i=some false := by
          by_cases h7 : i=7
          · simpa [h7] using seven
          · convert zero (i-8) (by omega) using 1 <;> congr 1 <;> omega
        rw [h]; decide)
  have p4 := keep (M := O) (P := 9+z) (oq 128) (oq 129) 6 7 T .right
    (by omega) (by omega) (by rw [six]; decide) rfl
  have p5 := hop (M := O) (P := 9+z) (oq 129) (oq 130) 7 8 T none .right
    (by omega) (by omega) (by rw [seven]; decide) rfl
  have p6 := sweepR (M := O) (P := 9+z) (oq 130) (put T 7 none) 8 z (by omega) (by
    intro i lo hi
    have h : put T 7 none i=some false := by
      simp only [put,if_neg (by omega : i≠7)]
      convert zero (i-8) (by omega) using 1 <;> congr 1 <;> omega
    rw [h]; decide)
  have p7 := keep (M := O) (P := 9+z) (oq 130) (oq 133) (8+z) (8+z) (put T 7 none) .stay
    (by omega) (by omega) (by simp only [put,if_neg (by omega : 8+z≠7),term]; decide) rfl
  convert ((((((p0.append p1).append p2).append p3).append p4).append p5).append p6).append p7 using 1 <;> omega
private theorem read_path (T : Nat → Option Bool) (z : Nat) (pos : 0<z)
    (zero : ∀ j, j<z → T (8+j)=some false) (term : T (8+z)=some true) :
    Path (M := O) (9+z) (2*z+3) ⟨oq 133,8+z,put T 7 none⟩
      ⟨oq 138,9+z,put (put T 7 none) 8 none⟩ := by
  let U := put T 7 none
  have uterm : U (8+z)=some true := by dsimp [U,put]; rw [if_neg (by omega),term]
  have uzero (i : Nat) (lo : 8 ≤ i) (hi : i < 8+z) : U i=some false := by
    dsimp [U,put]; rw [if_neg (by omega)]
    convert zero (i-8) (by omega) using 1 <;> congr 1 <;> omega
  have p0 := keep (M := O) (P := 9+z) (oq 133) (oq 134) (8+z) (7+z) U .left
    (by omega) (by omega) (by rw [uterm]; decide) (by simp [dest])
  have p1 := keep (M := O) (P := 9+z) (oq 134) (oq 135) (7+z) (6+z) U .left
    (by omega) (by omega) (by rw [uzero _ (by omega) (by omega)]; decide) (by simp [dest])
  have p2 : Path (M := O) (9+z) (z-1) ⟨oq 135,6+z,U⟩ ⟨oq 135,7,U⟩ := by
    simpa [show 7+(z-1)=6+z by omega] using
      sweepL (M := O) (P := 9+z) (oq 135) U 7 (z-1) (by omega) (by
        intro i lo hi
        rw [uzero i (by omega) (by omega)]; decide)
  have p3 := keep (M := O) (P := 9+z) (oq 135) (oq 136) 7 8 U .right
    (by omega) (by omega) (by
      have hn : U 7=none := by simp [U,put]
      rw [hn]; decide) rfl
  have p4 := hop (M := O) (P := 9+z) (oq 136) (oq 137) 8 9 U none .right
    (by omega) (by omega) (by rw [uzero 8 (by omega) (by omega)]; decide) rfl
  have p5 : Path (M := O) (9+z) (z-1) ⟨oq 137,9,put U 8 none⟩ ⟨oq 137,8+z,put U 8 none⟩ := by
    simpa [show 9+(z-1)=8+z by omega] using
      sweepR (M := O) (P := 9+z) (oq 137) (put U 8 none) 9 (z-1) (by omega) (by
        intro i lo hi
        simp only [put,if_neg (by omega : i≠8)]
        rw [uzero i (by omega) (by omega)]; decide)
  have p6 := keep (M := O) (P := 9+z) (oq 137) (oq 138) (8+z) (9+z) (put U 8 none) .right
    (by omega) (by omega) (by simp only [put,if_neg (by omega : 8+z≠8),uterm]; decide) (by dsimp [dest]; omega)
  convert (((((p0.append p1).append p2).append p3).append p4).append p5).append p6 using 1 <;> dsimp [U] <;> omega

private def source {a m : Nat} (x : Bitstring a) (w : Bitstring m) (i : Nat) : Option Bool :=
  if h : i<a+m then some (Fin.append x w ⟨i,h⟩)
  else if i=FixedRawLengthFence.fencePos (pairLength a m) then some false else none
private theorem source_eq {a m : Nat} (x : Bitstring a) (w : Bitstring m) (i : Nat)
    (hi : i<FixedRawLengthFence.fencePos (pairLength a m)) :
    source x w i=FixedContentTagGate.physicalSymbol (Fin.append x w) i := by
  unfold source FixedContentTagGate.physicalSymbol
  split_ifs <;> first | rfl | omega
private theorem price (R S z I v : Nat) (base : I≤16*(R+1)^2)
    (sr : S≤R) (zs : z≤S) (vv : v≤5*z+12) : I+3*S+7+v≤128*(R+1)^2 := by
  nlinarith [Nat.zero_le (R^2)]
attribute [local irreducible] UniformTM.run
/-- Actual raw producer checkpoint, before reading the first payload cell.
Width zero instead uses its two literal dispatch rows. Full finite tape retained. -/
theorem header_gate {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    let c := initialConfig SmallIngress.producer B (encodePair x w)
    ∃ t, t+3 ≤ 128*(pairLength a m+1)^2 ∧
      (z=0 → (SmallIngress.producer.run t c).state.val=133 ∧
        (SmallIngress.producer.run (t+1) c).state.val=134 ∧
        (SmallIngress.producer.run (t+2) c).state.val=161) ∧
      (0<z → ∃ h : 9+z < tapeLength (pairLength a m) B,
        SmallIngress.producer.run t c=⟨SmallIngress.q 138,⟨9+z,h⟩,
          Function.update (Function.update (FixedRawLengthFence.fencedContentTape B x w)
            ⟨7,by omega⟩ none)
            ⟨8,by omega⟩ none⟩) := by
  dsimp only
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let g := FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7
  let T := source x w
  obtain ⟨support,term,zero⟩ := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma
  have hS : 9+z≤a+m := by omega
  have ltF : a+m<FixedRawLengthFence.fencePos (pairLength a m) := by simp [FixedRawLengthFence.fencePos,pairLength]; omega
  obtain ⟨_,_,_,_,_,_,_,_,iffTag,_⟩ := FixedContentTagGate.tag_contract (Fin.append x w)
  have six : T 6=some true := by dsimp only [T]; rw [source_eq x w 6 (by omega)]; exact iffTag.mp tag ⟨6,by decide⟩
  have seven : T 7=some false := by dsimp only [T]; rw [source_eq x w 7 (by omega)]; exact iffTag.mp tag ⟨7,by decide⟩
  have zeros (j : Nat) (hj : j<z) : T (8+j)=some false := by dsimp only [T]; rw [source_eq x w _ (by omega)]; exact zero j hj
  have terminator : T (8+z)=some true := by dsimp only [T]; rw [source_eq x w _ (by omega)]; exact term
  have room : 9+z<tapeLength (pairLength a m) B := by
    dsimp only [B]
    have h := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
    simp only [tapeLength,pairLength] at *; omega
  have gp := gamma_path T z six seven zeros terminator
  have ge := gp.execute room
  have anchor : O.run (g+(3*z+6)) (initialConfig O B (encodePair x w))=
      embed (⟨oq 133,8+z,put T 7 none⟩ : Node O) (by change 8+z<tapeLength (pairLength a m) B; omega) := by
    rw [O.run_add,SmallIngress.raw_gamma_start x w tag]
    exact ge
  have budget := (FixedRawLengthFence.content_prefix_resources a m).2
  have clock : ∀ v, v≤5*z+12 → g+v≤128*(pairLength a m+1)^2 := by
    intro v hv
    dsimp [g] at *
    have sr : a+m≤pairLength a m := by simp only [pairLength]; omega
    exact price (pairLength a m) (a+m) z _ v (by simpa only [FixedRawLengthFence.allocation] using budget) sr (by omega) hv
  by_cases hz : z=0
  · subst z
    have a0 : O.run (g+6) (initialConfig O B (encodePair x w))=
        embed (⟨oq 133,8,put T 7 none⟩ : Node O) (by change 8<tapeLength (pairLength a m) B; omega) := by simpa using anchor
    have p0 := keep (M := O) (P := 9) (oq 133) (oq 134) 8 7 (put T 7 none) .left
      (by decide) (by decide) (by simp only [put,show (8:Nat)≠7 by decide,if_false,terminator]; decide) rfl
    have p1 := hop (M := O) (P := 9) (oq 134) (oq 161) 7 7 (put T 7 none) (some false) .stay
      (by decide) (by decide) (by change O.step (oq 134) none=_; decide) rfl
    have e0 := p0.execute room
    have e1 := (p0.append p1).execute room
    refine ⟨g+6,clock 9 (by omega),?_,by omega⟩
    intro _
    refine ⟨by rw [a0]; rfl,?_,?_⟩
    · rw [show g+6+1=(g+6)+1 by omega,O.run_add,a0]
      exact congrArg (fun c => c.state.val) e0
    · rw [O.run_add,a0]
      exact congrArg (fun c => c.state.val) e1
  · have pos : 0<z := by omega
    have full := gp.append (read_path T z pos zeros terminator)
    have exactRun := full.execute room
    refine ⟨g+(5*z+9),clock (5*z+12) le_rfl,by omega,?_⟩
    intro _
    refine ⟨room,?_⟩
    rw [O.run_add,SmallIngress.raw_gamma_start x w tag]
    have time : 3*z+6+(2*z+3)=5*z+9 := by omega
    change O.run (3*z+6+(2*z+3))
        ⟨oq 124,⟨8,by omega⟩,fun i => T i.val⟩=
        ⟨oq 138,⟨9+z,room⟩,fun i => put (put T 7 none) 8 none i.val⟩ at exactRun
    rw [time] at exactRun
    have h8 : 8<tapeLength (pairLength a m) B := by omega
    change O.run (5*z+9) ⟨oq 124,⟨8,h8⟩,fun i => T i.val⟩=_
    rw [exactRun]
    refine Config.ext_parts ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      simp only [put,Function.update_apply,Fin.ext_iff]
      rfl
end IngressRepair
