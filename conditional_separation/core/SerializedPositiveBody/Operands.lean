import SerializedPositiveBody.Frame
namespace SerializedPositiveBody
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
private def X (T : Nat → Option Bool) (D : Nat → Nat) (S M W v i : Nat) : Option Bool :=
  if i=M+v ∧ i < S then none else if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-v)) else
  if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ v)) else T i
private def second (b : Bool) : Fin 9 := if b then 2 else 1
private def third (a b : Bool) : Fin 9 := if a then if b then 6 else 5 else if b then 4 else 3
section LiteralDispatch
set_option maxRecDepth 4000
private theorem first_row (b : Bool) (m : Fin 3) :
    SerializedBody.machine.step (SerializedBodyRefinement.getExit 0 b m) none=
      (SerializedBodyRefinement.getEntry (second b) m,none,.stay) := by
  cases b <;> fin_cases m <;> rfl
private theorem second_row (a b : Bool) (m : Fin 3) :
    SerializedBody.machine.step (SerializedBodyRefinement.getExit (second a) b m) none=
      (SerializedBodyRefinement.getEntry (third a b) m,none,.stay) := by
  cases a <;> cases b <;> fin_cases m <;> rfl
end LiteralDispatch
private theorem get_safe (site : Fin 9) (m : Fin 3) : 4 ≤ (SerializedBodyRefinement.getEntry site m).val := by
  fin_cases site <;> fin_cases m <;> decide
private theorem stay {N B : Nat} (s q : Fin 7500) (T : Nat → Option Bool)
    (h : Fin (tapeLength N B)) (blank : T h.val=none)
    (row : SerializedBody.machine.step s none=(q,none,.stay)) :
    SerializedBody.machine.run 1 (⟨s,h,fun i=>T i.val⟩ : Config 7500 N B)=⟨q,h,fun i=>T i.val⟩ := by
  change SerializedBody.machine.stepConfig _=_
  apply Config.ext_parts
  · change (SerializedBody.machine.step s (T h.val)).1=q
    rw [blank,row]
  · apply Fin.ext
    change (moveHead h (SerializedBody.machine.step s (T h.val)).2.2).val=h.val
    rw [blank,row];rfl
  · funext i
    change (if i=h then (SerializedBody.machine.step s (T h.val)).2.1 else T i.val)=T i.val
    rw [blank,row]
    by_cases eq : i=h
    · subst i;simp only [↓reduceIte,blank]
    · simp only [if_neg eq]
private theorem append_through {N B t s : Nat} {a b : Config 7500 N B}
    (run : SerializedBody.machine.run t a=b)
    (before : ∀ u,u ≤ t → 4 ≤ (SerializedBody.machine.run u a).state.val)
    (afterwards : ∀ u,u ≤ s → 4 ≤ (SerializedBody.machine.run u b).state.val) :
    ∀ u,u ≤ t+s → 4 ≤ (SerializedBody.machine.run u a).state.val := by
  intro u hu
  by_cases early : u ≤ t
  · exact before u early
  · rw [show u=t+(u-t) by omega,SerializedBody.machine.run_add,run]
    exact afterwards (u-t) (by omega)
private theorem extend_one {N B t : Nat} {a b c : Config 7500 N B}
    (run : SerializedBody.machine.run t a=b) (hop : SerializedBody.machine.run 1 b=c)
    (before : ∀ u,u ≤ t → 4 ≤ (SerializedBody.machine.run u a).state.val) (safe : 4 ≤ c.state.val) :
    SerializedBody.machine.run (t+1) a=c ∧ ∀ u,u ≤ t+1 → 4 ≤ (SerializedBody.machine.run u a).state.val := by
  have total : SerializedBody.machine.run (t+1) a=c := by rw [SerializedBody.machine.run_add,run,hop]
  refine ⟨total,?_⟩
  intro u hu
  by_cases early : u ≤ t
  · exact before u early
  · have eq : u=t+1 := by omega
    rw [eq,total];exact safe
/-- All three literal tag reads with the actual finite dispatch rows; arbitrary physical/virtual window and installed assignment. -/
theorem tag_reader (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r M W u N B P : Nat) (source : Fin S → Bool)
    (enough : u+3 ≤ W) (hw : W ≤ r) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (eof : T S=none) (left : T L=none) (right : T H=none) (fence : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (sourceCells : ∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let V:=fun v i=>if i=M+v ∧ i < S then none else
      if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-v)) else
      if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ v)) else T i
    let b0:=padRead source (M+u); let b1:=padRead source (M+(u+1)); let b2:=padRead source (M+(u+2))
    let site : Fin 9:=if b0 then if b1 then 6 else 5 else if b1 then 4 else 3
    let initial : Config 7500 N B:=⟨SerializedBodyRefinement.getEntry 0 (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>V u i.val⟩
    (∀ j : Fin 3,(SerializedBody.window source M W)[u+j.val]?=some (padRead source (M+(u+j.val)))) ∧
    ∃ t,t ≤ 256*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBodyRefinement.getExit site b2 (SerializedBody.sourceMode source (M+(u+3))),⟨D 0,h0⟩,fun i=>V (u+3) i.val⟩ ∧
      ∀ j,j ≤ t → 4 ≤ (SerializedBody.machine.run j initial).state.val := by
  dsimp only
  have read (call : Fin 9) (v : Nat) (hv : v < W) :=positive_reader call D T S L H Q F r M W v N B P source hv hw sl lh positive arena anchor rise mono blank cells len4 len11 eof left right fence reg ass marks gap sourceCells room fit h0
  have atZero (v : Nat) : X T D S M W v (D 0)=none := by
    have b4:=mono 0 4 (by decide) (by decide)
    have b11:=mono 0 11 (by decide) (by decide)
    have before : S < D 0 := by omega
    simp only [X,if_neg (by omega : ¬(D 0=M+v ∧ D 0 < S)),
      if_neg (by omega : ¬(D 4 < D 0 ∧ D 0 < D 5)),if_neg (by omega : ¬(D 11 < D 0 ∧ D 0 < D 12)),blank 0 (by decide)]
  obtain ⟨_,t0,p0,r0,f0⟩:=read 0 u (by omega)
  let b0:=padRead source (M+u)
  let b1:=padRead source (M+(u+1))
  let b2:=padRead source (M+(u+2))
  have hop0:=stay (SerializedBodyRefinement.getExit 0 b0 (SerializedBody.sourceMode source (M+(u+1))))
    (SerializedBodyRefinement.getEntry (second b0) (SerializedBody.sourceMode source (M+(u+1))))
    (X T D S M W (u+1)) ⟨D 0,h0⟩ (atZero _) (first_row _ _)
  obtain ⟨e0,g0⟩:=extend_one r0 hop0 f0 (get_safe _ _)
  obtain ⟨_,t1,p1,r1,f1⟩:=read (second b0) (u+1) (by omega)
  let A : Config 7500 N B:=⟨SerializedBodyRefinement.getEntry 0 (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>X T D S M W u i.val⟩
  have combined1 : SerializedBody.machine.run (t0+1+t1) A=⟨SerializedBodyRefinement.getExit (second b0) b1 (SerializedBody.sourceMode source (M+(u+1+1))),⟨D 0,h0⟩,fun i=>X T D S M W (u+1+1) i.val⟩ := by
    rw [SerializedBody.machine.run_add]
    exact (congrArg (SerializedBody.machine.run t1) e0).trans r1
  have through1:=append_through e0 g0 f1
  have hop1:=stay (SerializedBodyRefinement.getExit (second b0) b1 (SerializedBody.sourceMode source (M+(u+2))))
    (SerializedBodyRefinement.getEntry (third b0 b1) (SerializedBody.sourceMode source (M+(u+2))))
    (X T D S M W (u+2)) ⟨D 0,h0⟩ (atZero _) (second_row _ _ _)
  have r1' : SerializedBody.machine.run (t0+1+t1) A=⟨SerializedBodyRefinement.getExit (second b0) b1 (SerializedBody.sourceMode source (M+(u+2))),⟨D 0,h0⟩,fun i=>X T D S M W (u+2) i.val⟩ := by
    simpa only [Nat.add_assoc] using combined1
  obtain ⟨e1,g1⟩:=extend_one r1' hop1 through1 (get_safe _ _)
  obtain ⟨_,t2,p2,r2,f2⟩:=read (third b0 b1) (u+2) (by omega)
  have total : SerializedBody.machine.run (t0+1+t1+1+t2) A=⟨SerializedBodyRefinement.getExit (third b0 b1) b2 (SerializedBody.sourceMode source (M+(u+2+1))),⟨D 0,h0⟩,fun i=>X T D S M W (u+2+1) i.val⟩ := by
    rw [SerializedBody.machine.run_add]
    exact (congrArg (SerializedBody.machine.run t2) e1).trans r2
  have through:=append_through e1 g1 f2
  refine ⟨?_,t0+1+t1+1+t2,by omega,?_,through⟩
  · intro j
    simp only [SerializedBody.window,List.getElem?_ofFn,show u+j.val < W by have :=j.isLt;omega,↓reduceDIte]
  · simpa only [Nat.add_assoc] using total
end SerializedPositiveBody
