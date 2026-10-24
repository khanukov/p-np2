import AllArityWorkspace.Target
namespace AllArityWorkspace
open Pnp3.Complexity.Uniform.V1
/-- Pointwise meaning of the exact full tape exported at q201. Empty banks
are allowed: n0 has adjacent delimiters F+r+2 and F+r+n+3. -/
theorem six_bank_image (C : Nat → Option Bool) (L n F r : Nat)
    (room : L+n+1 < F) (fence : C F=some false) (d0 : C (F+1)=none)
    (bank0 : ∀ i, F+1 < i → i < F+r+2 → C i=some true)
    (fresh : ∀ i, F+r+2 ≤ i → i ≤ F+5*r+n+7 → C i=none) :
    (∀ i, L < i → i < L+n+1 → CappedWorkspace.Target.image C L n F r i=some true) ∧
    CappedWorkspace.Target.image C L n F r F=some false ∧
    (∀ i, F+1 < i → i < F+r+2 → CappedWorkspace.Target.image C L n F r i=some true) ∧
    (∀ i, (F+r+2 < i ∧ i < F+r+n+3) ∨
      (F+r+n+3 < i ∧ i < F+2*r+n+4) ∨
      (F+2*r+n+4 < i ∧ i < F+3*r+n+5) ∨
      (F+3*r+n+5 < i ∧ i < F+4*r+n+6) ∨
      (F+4*r+n+6 < i ∧ i < F+5*r+n+7) →
        CappedWorkspace.Target.image C L n F r i=some false) ∧
    (∀ d, d=F+1 ∨ d=F+r+2 ∨ d=F+r+n+3 ∨ d=F+2*r+n+4 ∨
      d=F+3*r+n+5 ∨ d=F+4*r+n+6 ∨ d=F+5*r+n+7 →
        CappedWorkspace.Target.image C L n F r d=none) ∧
    (∀ i, i ≤ L ∨ (L+n+1 ≤ i ∧ i ≤ F+1) ∨ F+5*r+n+7 ≤ i →
      CappedWorkspace.Target.image C L n F r i=C i) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i lo hi
    unfold CappedWorkspace.Target.image
    rw [if_pos ⟨lo,hi⟩]
  · unfold CappedWorkspace.Target.image
    rw [if_neg (by omega),if_neg (by omega)]
    exact fence
  · intro i lo hi
    unfold CappedWorkspace.Target.image
    rw [if_neg (by omega),if_neg (by omega)]
    exact bank0 i lo hi
  · intro i hi
    unfold CappedWorkspace.Target.image
    rw [if_neg (by omega),if_pos hi]
  · intro d hd
    have untouched : CappedWorkspace.Target.image C L n F r d=C d := by
      unfold CappedWorkspace.Target.image
      rw [if_neg (by omega),if_neg (by omega)]
    rw [untouched]
    by_cases first : d=F+1
    · subst d; exact d0
    · exact fresh d (by omega) (by omega)
  · intro i hi
    unfold CappedWorkspace.Target.image
    rw [if_neg (by omega),if_neg (by omega)]
theorem Audit.check_six_bank_image (C : Nat → Option Bool) (L n F r : Nat)
    (room : L+n+1 < F) (fence : C F=some false) (d0 : C (F+1)=none)
    (bank0 : ∀ i, F+1 < i → i < F+r+2 → C i=some true)
    (fresh : ∀ i, F+r+2 ≤ i → i ≤ F+5*r+n+7 → C i=none) :
    (∀ i, L < i → i < L+n+1 → CappedWorkspace.Target.image C L n F r i=some true) ∧
    CappedWorkspace.Target.image C L n F r F=some false ∧
    (∀ i, F+1 < i → i < F+r+2 → CappedWorkspace.Target.image C L n F r i=some true) ∧
    (∀ i, (F+r+2 < i ∧ i < F+r+n+3) ∨
      (F+r+n+3 < i ∧ i < F+2*r+n+4) ∨
      (F+2*r+n+4 < i ∧ i < F+3*r+n+5) ∨
      (F+3*r+n+5 < i ∧ i < F+4*r+n+6) ∨
      (F+4*r+n+6 < i ∧ i < F+5*r+n+7) →
        CappedWorkspace.Target.image C L n F r i=some false) ∧
    (∀ d, d=F+1 ∨ d=F+r+2 ∨ d=F+r+n+3 ∨ d=F+2*r+n+4 ∨
      d=F+3*r+n+5 ∨ d=F+4*r+n+6 ∨ d=F+5*r+n+7 →
        CappedWorkspace.Target.image C L n F r d=none) ∧
    (∀ i, i ≤ L ∨ (L+n+1 ≤ i ∧ i ≤ F+1) ∨ F+5*r+n+7 ≤ i →
      CappedWorkspace.Target.image C L n F r i=C i) :=
  @AllArityWorkspace.six_bank_image C L n F r room fence d0 bank0 fresh
end AllArityWorkspace
#print axioms AllArityWorkspace.six_bank_image
#print axioms AllArityWorkspace.Audit.check_six_bank_image
