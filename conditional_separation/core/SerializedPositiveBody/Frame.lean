import SerializedBodyCompletion.Audit
namespace SerializedPositiveBody
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
private def counters (T : Nat → Option Bool) (D : Nat → Nat) (W u i : Nat) : Option Bool :=
  if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-u)) else
  if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ u)) else T i
private def view (T : Nat → Option Bool) (D : Nat → Nat) (S M W u i : Nat) : Option Bool :=
  if i=M+u ∧ i < S then none else counters T D W u i
private theorem disjoint (D : Nat → Nat) (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    {i j k : Nat} (hj : j < 12) (hk : k < 12) (ne : j≠k)
    (lo : D j < i) (hi : i < D (j+1)) : ¬(D k < i ∧ i < D (k+1)) := by
  by_cases order : j < k
  · have :=mono (j+1) k (by omega) (by omega);omega
  · have :=mono (k+1) j (by omega) (by omega);omega
private theorem below (T : Nat → Option Bool) (D : Nat → Nat) (W u i : Nat)
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (hi : i < D 0) : counters T D W u i=T i := by
  have a:=mono 0 4 (by decide) (by decide)
  have b:=mono 0 11 (by decide) (by decide)
  simp only [counters,if_neg (by omega : ¬(D 4 < i ∧ i < D 5)),if_neg (by omega : ¬(D 11 < i ∧ i < D 12))]
private theorem nonfield (D : Nat → Nat) (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (j k : Nat) (hj : j ≤ 12) (hk : k < 12) : ¬(D k < D j ∧ D j < D (k+1)) := by
  by_cases order : j ≤ k
  · have :=mono j k order (by omega);omega
  · have :=mono (k+1) j (by omega) hj;omega
private theorem view_sep (T : Nat → Option Bool) (D : Nat → Nat) (S M W u j : Nat)
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (before : S < D 0) (hj : j ≤ 12) : view T D S M W u (D j)=T (D j) := by
  have :=mono 0 j (by omega) hj
  simp only [view,if_neg (by omega : ¬(D j=M+u ∧ D j < S)),counters,
    if_neg (nonfield D mono j 4 hj (by decide)),if_neg (nonfield D mono j 11 hj (by decide))]
private theorem view_inside (T : Nat → Option Bool) (D : Nat → Nat) (S M W u j i : Nat)
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (before : S < D 0)
    (hj : j < 12) (lo : D j < i) (_hi : i < D (j+1)) :
    view T D S M W u i=counters T D W u i := by
  have :=mono 0 j (by omega) (by omega)
  simp only [view,if_neg (by omega : ¬(i=M+u ∧ i < S))]
private theorem counter_tick (T : Nat → Option Bool) (D : Nat → Nat) (W u r i : Nat)
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (hu : u < W) (hw : W ≤ r)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1) :
    (if i=D 11+u+1 then some true else if i=D 4+(W-u) then some false else counters T D W u i)=
      counters T D W (u+1) i := by
  have inc : D 11 < D 11+u+1 ∧ D 11+u+1 < D 12 := by omega
  have dec : D 4 < D 4+(W-u) ∧ D 4+(W-u) < D 5 := by omega
  by_cases a : D 4 < i ∧ i < D 5
  · have no11:=disjoint D mono (by decide) (by decide) (by decide : 4≠11) a.1 a.2
    have notInc : i≠D 11+u+1 := by intro eq;subst i;exact no11 inc
    simp only [if_neg notInc,counters,if_pos a]
    by_cases atDec : i=D 4+(W-u)
    · rw [if_pos atDec]
      have no : ¬i-D 4 ≤ W-(u+1) := by omega
      simp only [no,decide_false]
    · rw [if_neg atDec]
      by_cases yes : i-D 4 ≤ W-u
      · have yesNext : i-D 4 ≤ W-(u+1) := by omega
        simp only [yes,yesNext,decide_true]
      · have noNext : ¬i-D 4 ≤ W-(u+1) := by omega
        simp only [yes,noNext,decide_false]
  · by_cases b : D 11 < i ∧ i < D 12
    · have notDec : i≠D 4+(W-u) := by intro eq;subst i;exact a dec
      simp only [counters,if_neg a,if_pos b]
      by_cases atInc : i=D 11+u+1
      · rw [if_pos atInc]
        have yes : i-D 11 ≤ u+1 := by omega
        simp only [yes,decide_true]
      · rw [if_neg atInc,if_neg notDec]
        by_cases yes : i-D 11 ≤ u
        · have yesNext : i-D 11 ≤ u+1 := by omega
          simp only [yes,yesNext,decide_true]
        · have noNext : ¬i-D 11 ≤ u+1 := by omega
          simp only [yes,noNext,decide_false]
    · have notInc : i≠D 11+u+1 := by intro eq;subst i;exact b inc
      have notDec : i≠D 4+(W-u) := by intro eq;subst i;exact a dec
      simp only [if_neg notInc,if_neg notDec,counters,if_neg a,if_neg b]
private theorem image_tick (T : Nat → Option Bool) (D : Nat → Nat) (S M W u r : Nat)
    (source : Fin S → Bool) (before : S < D 0) (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (hu : u < W) (hw : W ≤ r) (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (eof : T S=none) (src : ∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let X:=view T D S M W u
    let C:=fun i=>if i=D 11+u+1 then some true else if i=D 4+(W-u) then some false else X i
    (fun i=>if M+u < S then if i=M+u+1 then none else if i=M+u then some (padRead source (M+u)) else C i else C i)=
      view T D S M W (u+1) := by
  dsimp only
  have lo4:=mono 0 4 (by decide) (by decide)
  have lo11:=mono 0 11 (by decide) (by decide)
  have patch (i : Nat) (no : ¬(i=M+u ∧ i < S)) :
      (if i=D 11+u+1 then some true else if i=D 4+(W-u) then some false else view T D S M W u i)=counters T D W (u+1) i := by
    simp only [view,if_neg no]
    exact counter_tick T D W u r i mono hu hw len4 len11
  funext i
  by_cases physical : M+u < S
  · rw [if_pos physical]
    by_cases next : i=M+u+1
    · rw [if_pos next]
      by_cases hp : i < S
      · rw [view,if_pos (show i=M+(u+1) ∧ i < S from ⟨by omega,hp⟩)]
      · have ie : i=S := by omega
        have no : ¬(i=M+(u+1) ∧ i < S) := by omega
        rw [view,if_neg no,below T D W (u+1) i mono (by omega),ie,eof]
    · rw [if_neg next]
      by_cases current : i=M+u
      · rw [if_pos current]
        have no : ¬(i=M+(u+1) ∧ i < S) := by omega
        rw [view,if_neg no,below T D W (u+1) i mono (by omega)]
        subst i
        simpa only [padRead,physical,↓reduceDIte] using (src (M+u) (by omega) physical).symm
      · rw [if_neg current,patch i (by omega)]
        simp only [view,if_neg (by omega : ¬(i=M+(u+1) ∧ i < S))]
  · rw [if_neg physical,patch i (by omega)]
    simp only [view,if_neg (by omega : ¬(i=M+(u+1) ∧ i < S))]
/-- Positive native Get on a persistent original source/counter image, for every site and carry mode. -/
theorem positive_reader (site : Fin 9) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r M W u N B P : Nat) (source : Fin S → Bool)
    (hu : u < W) (hw : W ≤ r) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (eof : T S=none) (left : T L=none) (right : T H=none) (fence : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (sourceCells : ∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let X:=fun v i=>if i=M+v ∧ i < S then none else
      if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-v)) else
      if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ v)) else T i
    let initial : Config 7500 N B:=⟨SerializedBodyRefinement.getEntry site (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>X u i.val⟩
    (SerializedBody.window source M W)[u]?=some (padRead source (M+u)) ∧
    ∃ t,t ≤ 64*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBodyRefinement.getExit site (padRead source (M+u)) (SerializedBody.sourceMode source (M+(u+1))),⟨D 0,h0⟩,fun i=>X (u+1) i.val⟩ ∧
      ∀ j,j ≤ t → 4 ≤ (SerializedBody.machine.run j initial).state.val := by
  dsimp only
  have before : S < D 0 := by omega
  let X:=view T D S M W u
  have small (i : Nat) (bound : i < D 0) : X i=(if i=M+u ∧ i < S then none else T i) := by
    simp only [X,view,below T D W u i mono bound]
  have header (i : Nat) (lo : S ≤ i) (hi : i < D 0) : X i=T i := by
    rw [small i hi,if_neg (by omega : ¬(i=M+u ∧ i < S))]
  have occupied (j i : Nat) (hj : j < 12) (lo : D j < i) (hi : i < D (j+1)) : ∃ b,X i=some b := by
    rw [show X i=counters T D W u i from view_inside T D S M W u j i mono before hj lo hi]
    by_cases a : D 4 < i ∧ i < D 5
    · exact ⟨decide (i-D 4 ≤ W-u),by simp only [counters,if_pos a]⟩
    by_cases b : D 11 < i ∧ i < D 12
    · exact ⟨decide (i-D 11 ≤ u),by simp only [counters,if_neg a,if_pos b]⟩
    obtain ⟨v,hv⟩:=cells j i hj lo hi
    exact ⟨v,by simp only [counters,if_neg a,if_neg b];exact hv⟩
  have rem (i : Nat) (lo : D 4 < i) (hi : i < D 5) : X i=some (decide (i-D 4 ≤ W-u)) := by
    rw [show X i=counters T D W u i from view_inside T D S M W u 4 i mono before (by decide) lo hi]
    exact if_pos ⟨lo,hi⟩
  have used (i : Nat) (lo : D 11 < i) (hi : i < D 12) : X i=some (decide (i-D 11 ≤ u)) := by
    rw [show X i=counters T D W u i from view_inside T D S M W u 11 i mono before (by decide) lo hi]
    simp only [counters,if_neg (disjoint D mono (by decide) (by decide) (by decide : 11≠4) lo hi),if_pos (show D 11 < i ∧ i < D 12 from ⟨lo,hi⟩)]
  obtain ⟨t,price,run,prefixBound⟩:=SerializedBodyRefinement.reader site D X S L H Q F r (W-u) u (M+u) N B P source (by omega) sl lh positive arena anchor rise mono
    (by intro j hj;rw [show X (D j)=T (D j) from view_sep T D S M W u j mono before hj];exact blank j hj)
    occupied len4 len11 rem used
    (by rw [header S le_rfl before];exact eof)
    (by rw [header L (by omega) (by omega)];exact left)
    (by rw [header H (by omega) (by omega)];exact right)
    (by rw [header F (by omega) (by omega)];exact fence)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact reg i lo hi)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact ass i lo hi)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact gap i lo hi)
    (by intro physical;rw [small (M+u) (by omega),if_pos ⟨rfl,physical⟩])
    (by intro i lo hi;rw [small i (by omega),if_neg (by omega : ¬(i=M+u ∧ i < S))];exact sourceCells i (by omega) hi)
    room fit h0
  have nonzero : W-u≠0 := by omega
  dsimp only at run
  simp only [if_neg nonzero] at run
  have finalTape:=image_tick T D S M W u r source before mono hu hw len4 len11 eof sourceCells
  dsimp only at finalTape
  have finiteTape:=congrArg (fun f : Nat → Option Bool=>fun i : Fin (tapeLength N B)=>f i.val) finalTape
  change SerializedBody.machine.run t _=⟨SerializedBodyRefinement.getExit site (padRead source (M+u)) (SerializedBody.sourceMode source (M+u+1)),⟨D 0,h0⟩,_⟩ at run
  dsimp only at finiteTape
  dsimp only [X] at run
  rw [finiteTape] at run
  refine ⟨?_,t,price,?_,prefixBound⟩
  · simp only [SerializedBody.window,List.getElem?_ofFn,hu,↓reduceDIte]
  · simpa only [Nat.add_assoc] using run
end SerializedPositiveBody
