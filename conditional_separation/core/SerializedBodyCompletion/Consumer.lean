import SerializedBodyCompletion.Kernel
namespace SerializedBodyCompletion
open Pnp3.Complexity.Uniform.V1
/-- Complete strict-exhaustion consumer: SAME actual Get -> live abort -> FIRST literal reject/H. -/
theorem exhausted_consumer (site : Fin 9) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r used c N B P : Nat) (source : Fin S → Bool)
    (bounded : used ≤ r) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (remaining : ∀ i,D 4 < i → i < D 5 → T i=some false)
    (consumed : ∀ i,D 11 < i → i < D 12 → T i=some (decide (i-D 11 ≤ used)))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) (hH : H < tapeLength N B)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let clearedTape : Nat → Option Bool:=fun i=>if D 10 < i ∧ i < D 11 then some true else
      if [1,4,5,6,8,9,11].any (fun j=>decide (D j < i ∧ i < D (j+1))) then some false else T i
    let initial : Config 7500 N B:=⟨SerializedBodyRefinement.getEntry site (SerializedBody.sourceMode source c),⟨D 0,h0⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 1024*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else clearedTape i.val else clearedTape i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := by
  have rem : ∀ i,D 4 < i → i < D 5 → T i=some (decide (i-D 4 ≤ 0)) := by
    intro i lo hi;rw [remaining i lo hi];simp only [show ¬i-D 4 ≤ 0 by omega,decide_false]
  obtain ⟨readTime,readPrice,readRun,readPrefix⟩:=SerializedBodyRefinement.reader site D T S L H Q F r 0 used c N B P source
    (by omega) sl lh positive arena anchor rise mono blank cells len4 len11 rem consumed ts tl th tf reg ass marks gap hole src room fit h0
  dsimp only at readRun readPrefix
  obtain ⟨cleanTime,cleanPrice,cleanRun,cleanPrefix⟩:=abort_cleanup D T S L H Q F c N B P source sl lh positive arena anchor rise mono blank cells room fit h0 hH ts tl th tf reg ass marks gap hole src
  refine ⟨readTime+cleanTime,by omega,?_,?_⟩
  · rw [SerializedBody.machine.run_add,readRun]
    exact cleanRun
  · intro u hu
    by_cases earlier : u ≤ readTime
    · exact readPrefix u earlier
    · rw [show u=readTime+(u-readTime) by omega,SerializedBody.machine.run_add,readRun]
      exact cleanPrefix (u-readTime) (by omega)
#print axioms SerializedBodyCompletion.exhausted_consumer
end SerializedBodyCompletion
