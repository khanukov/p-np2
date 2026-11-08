import PhysicalCallerClosure.ResetReady
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
theorem reset_body_entry_mirror (k : Nat) (a : Fin 3) (N B S L H M Q F P r g W : Nat)
    (D : Nat → Nat) (T : Nat → Option Bool) (source : Fin S → Bool)
    (rise:∀ j,j < 13 → D j < D (j+1))
    (mono:∀ i j,i ≤ j → j ≤ 13 → D i ≤ D j)
    (blank:∀ j,j ≤ 13 → T (D j)=none)
    (cells:∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (d0:D 0=F+1) (room:D 13 ≤ P) (fit:P < tapeLength N B)
    (width:∀ j,j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+r+1)
    (ug:∀ i,D 0 < i → i < D 1 → T i=some (decide (i-D 0 ≤ g)))
    (uw:∀ i,D 3 < i → i < D 4 → T i=some (decide (i-D 3 ≤ W)))
    (hg:g ≤ r) (hw:W ≤ r) (positive:0 < Q) (arena:H+Q < F)
    (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (sl:S < L) (lh:L < H) (ts:T S=none) (tl:T L=none)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b)
    (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (tag:a.val=2 ↔ S ≤ M) (anchor:M < S → 0 < M ∧ T (M-1)=none)
    (hH:H < tapeLength N B) :
    let initial : Config (callerMachine k).stateCount N B:=⟨resetEntry k a,⟨H,hH⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 1024*(r+1)*(P+1) ∧ (callerMachine k).run t initial=
      ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,hH⟩,fun h=>
        if h.val=M ∧ h.val < S then none
        else if D 6 < h.val ∧ h.val < D 7 then some (decide (h.val-D 6 ≤ g))
        else if D 4 < h.val ∧ h.val < D 5 then some (decide (h.val-D 4 ≤ W))
        else if D 11 < h.val ∧ h.val < D 12 then some false
        else if D 5 < h.val ∧ h.val < D 6 then some false else T h.val⟩ ∧
    (∀ u,u ≤ t → ((callerMachine k).run u initial).head.val ≤ P ∧
      ∀ i:Fin (tapeLength N B),P < i.val → ((callerMachine k).run u initial).tape i=T i.val) ∧
    (∀ u,u < t → ((callerMachine k).run u initial).state≠(callerMachine k).accept ∧
      ((callerMachine k).run u initial).state≠(callerMachine k).reject ∧
      ((callerMachine k).run u initial).state≠rowsDone k) ∧
      (∀ u,u < t → (BodyIngress.machine k).stateCount+7500 ≤ ((callerMachine k).run u initial).state.val) :=
  reset_body_entry k a N B S L H M Q F P r g W D T source rise mono blank cells d0 room fit width ug uw hg hw positive arena th tf marks gap sl lh ts tl reg beta src tag anchor hH
#print axioms reset_body_entry
#print axioms reset_body_entry_mirror
end PhysicalCallerClosure
