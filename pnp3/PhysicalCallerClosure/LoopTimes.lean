import PhysicalCallerClosure.RowRound
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1
private theorem one_price (q price unit : Nat) (bound:price ≤ unit) : price ≤ (q+1)*unit :=
  bound.trans (Nat.le_mul_of_pos_left unit (Nat.succ_pos q))
private theorem join_price (q first rest unit : Nat) (a:first ≤ unit) (b:rest ≤ q*unit) :
    first+rest ≤ (q+1)*unit := by
  rw [Nat.add_mul,Nat.one_mul]
  omega
private theorem only_start {M : UniformTM} {N B : Nat}
    (c : Config M.stateCount N B) (target : Nat → Config M.stateCount N B)
    (good : Nat → Prop) (row limit ready elapsed : Nat)
    (paid:M.run ready c=target row) (before:ready < elapsed)
    (stop:∀ i,row ≤ i → i < limit → (∀ j,row ≤ j → j < i → good j) → i=row) :
    ∃ starts : Nat → Nat,
      (∀ i,row ≤ i → i < limit → (∀ j,row ≤ j → j < i → good j) →
        starts i < elapsed ∧ M.run (starts i) c=target i) ∧
      (∀ i j,row ≤ i → i < j → j < limit → (∀ v,row ≤ v → v < j → good v) → starts i < starts j) := by
  refine ⟨(fun _=>ready),?_,?_⟩
  · intro i lo hi prior
    have eq:=stop i lo hi prior
    subst i
    exact ⟨before,paid⟩
  · intro i j lo lt hi prior
    have eq:=stop j (by omega) hi prior
    omega
private theorem prepend_starts {M : UniformTM} {N B : Nat}
    (c d : Config M.stateCount N B) (target : Nat → Config M.stateCount N B)
    (good : Nat → Prop) (row limit ready elapsed restTime : Nat) (restStarts : Nat → Nat)
    (step:M.run elapsed c=d) (paid:M.run ready c=target row) (before:ready < elapsed)
    (restPaid:∀ i,row+1 ≤ i → i < limit → (∀ j,row+1 ≤ j → j < i → good j) →
      restStarts i < restTime ∧ M.run (restStarts i) d=target i)
    (restOrder:∀ i j,row+1 ≤ i → i < j → j < limit →
      (∀ v,row+1 ≤ v → v < j → good v) → restStarts i < restStarts j) :
    ∃ starts : Nat → Nat,
      (∀ i,row ≤ i → i < limit → (∀ j,row ≤ j → j < i → good j) →
        starts i < elapsed+restTime ∧ M.run (starts i) c=target i) ∧
      (∀ i j,row ≤ i → i < j → j < limit → (∀ v,row ≤ v → v < j → good v) → starts i < starts j) := by
  let starts (i:Nat):=if i=row then ready else elapsed+restStarts i
  refine ⟨starts,?_,?_⟩
  · intro i lo hi prior
    by_cases eq:i=row
    · subst i
      simp only [starts,ite_true]
      exact ⟨by omega,paid⟩
    · obtain ⟨b,run⟩:=restPaid i (by omega) hi (by intro j jl jh;exact prior j (by omega) jh)
      simp only [starts,if_neg eq]
      refine ⟨by omega,?_⟩
      rw [UniformTM.run_add,step]
      exact run
  · intro i j lo lt hi prior
    have jNe:j≠row:=by omega
    simp only [starts,if_neg jNe]
    by_cases eq:i=row
    · rw [if_pos eq];omega
    · rw [if_neg eq]
      exact Nat.add_lt_add_left (restOrder i j (by omega) lt hi (by intro v vl vh;exact prior v (by omega) vh)) elapsed
end PhysicalCallerClosure
