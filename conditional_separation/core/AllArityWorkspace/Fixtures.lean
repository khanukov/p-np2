import AllArityWorkspace.Runtime
namespace AllArityWorkspace.Fixtures
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
attribute [local irreducible] UniformTM.run
private def layout (hole marker p S z n : Nat) (b : Bool) : Nat → Option Bool := fun i =>
  if i=hole then none else if i=marker then some true else if i=p then some b
  else if i < S ∨ S < i ∧ i < S+z+2 then some false
  else if S+z+2 < i ∧ i < S+z+n+3 then some false
  else if S+z+n+3 < i ∧ i ≤ S+z+n+3+2^n then some true
  else if i=53 then some false else none
private theorem headFit (S z n Q : Nat) (room : S+z+n+3+Q < 53) :
    S < tapeLength 17 (FixedRawLengthFence.allocation 17) := by
  have bound : S < 53 := by omega
  exact bound.trans (by decide)
private theorem setup (hole marker p S z n : Nat) (b : Bool)
    (hh : hole < p) (hm : marker < p) (unit : p+1=S) (room : S+z+n+3+2^n < 53)
    (fit : 53+5*(S-p)+n+7 < tapeLength 17 (FixedRawLengthFence.allocation 17)) :
    let B := FixedRawLengthFence.allocation 17
    let V := layout hole marker p S z n b
    let C := SuffixCap.Target.image V 53 (S-p)
    ∃ v, v ≤ 128*(n+(S-p)+1)*(53+5*(S-p)+n+9) ∧
      (AllArityCursor.machine 0).run v
        (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          (⟨Cursor.rReady 0,⟨S,headFit S z n (2^n) room⟩,fun i => C i.val⟩ : Config (Cursor.machine 0).stateCount 17 B))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          ⟨Cursor.q 0 201,⟨54,by decide⟩,fun i => CappedWorkspace.Target.image C (S+z+2) n 53 (S-p) i.val⟩ := by
  let B := FixedRawLengthFence.allocation 17
  let V := layout hole marker p S z n b
  let C := SuffixCap.Target.image V 53 (S-p)
  have geo : S+z+n+3 < 53 := lt_of_le_of_lt (Nat.le_add_right _ _) room
  have low (i : Nat) (hi : i ≤ 54) : C i=V i := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_neg (by omega)]
  have eof : C S=none := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have reg (i : Nat) (lo : S < i) (hi : i < S+z+2) : C i=some false := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (Or.inr ⟨lo,hi⟩)]
  have sep : C (S+z+2)=none := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have assn (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+2+n+1) : C i=some false := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by constructor <;> omega)]
  have right : C (S+z+2+n+1)=none := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have marks (i : Nat) (lo : S+z+2+n+1 < i) (hi : i ≤ S+z+2+n+1+2^n) : C i=some true := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by constructor <;> omega)]
  have gap (i : Nat) (lo : S+z+2+n+1+2^n < i) (hi : i < 53) : C i=none := by
    have plus : S+z+2+n+1 ≤ S+z+2+n+1+2^n := Nat.le_add_right _ _
    have afterH : S+z+n+3 < i := by clear * - plus lo; omega
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have fence : C 53=some false := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos rfl]
  have d0 : C 54=none := by
    rw [low _ (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have bank0 (i : Nat) (lo : 53+1 < i) (hi : i < 53+(S-p)+2) : C i=some true := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_pos (by omega)]
  have fresh (i : Nat) (lo : 53+(S-p)+2 ≤ i) (hi : i ≤ 53+5*(S-p)+n+7) : C i=none := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_neg (by omega)]
    dsimp only [V,layout]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  obtain ⟨v,hv,done,_first⟩ := CappedWorkspace.workspace 0 17 B S (S+z+2) n (2^n) 53 (S-p) C
    (by omega) (by positivity) (by omega) eof reg sep assn right marks gap fence d0 bank0 fresh fit
  refine ⟨v,hv,?_⟩
  change (SmallIngress.producer.seq (Cursor.machine 0)).run v _=_
  rw [UniformTM.seq_run_right,done]
/-- Complete prepared COUNTED plus six-bank body for n0/1/2; not a raw accepted word. -/
theorem workspace_false (n : Fin 3) :
    let z := if n.val=0 then 0 else 1
    let hole := if n.val=0 then 7 else 9
    let marker := if n.val=0 then 8 else 10
    let p := 9+2*z+2^n.val
    let S := p+1
    let B := FixedRawLengthFence.allocation 17
    let V : Nat → Option Bool := fun i =>
      if i=hole then none else if i=marker then some true else if i=p then some false
      else if i < S ∨ S < i ∧ i < S+z+2 then some false
      else if S+z+2 < i ∧ i < S+z+n.val+3 then some false
      else if S+z+n.val+3 < i ∧ i ≤ S+z+n.val+3+2^n.val then some true
      else if i=53 then some false else none
    let C := SuffixCap.Target.image V 53 (S-p)
    ∃ v, v ≤ 128*(n.val+(S-p)+1)*(53+5*(S-p)+n.val+9) ∧
      (AllArityCursor.machine 0).run ((2+(S-p)*(2*(53-p)+6))+v)
        (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount 17 B))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          ⟨Cursor.q 0 201,⟨54,by decide⟩,fun i => CappedWorkspace.Target.image C (S+z+2) n.val 53 (S-p) i.val⟩ := by
  dsimp only
  obtain ⟨v,hv,done⟩ := setup (if n.val=0 then 7 else 9) (if n.val=0 then 8 else 10)
    (9+2*(if n.val=0 then 0 else 1)+2^n.val) (9+2*(if n.val=0 then 0 else 1)+2^n.val+1)
    (if n.val=0 then 0 else 1) n.val false (by fin_cases n <;> decide) (by fin_cases n <;> decide)
    rfl (by fin_cases n <;> decide) (by fin_cases n <;> decide)
  refine ⟨v,hv,?_⟩
  rw [UniformTM.run_add,AllArityCounted.Fixtures.counted_false n]
  exact done
theorem check_workspace_false (n : Fin 3) :
    let z := if n.val=0 then 0 else 1
    let hole := if n.val=0 then 7 else 9
    let marker := if n.val=0 then 8 else 10
    let p := 9+2*z+2^n.val
    let S := p+1
    let B := FixedRawLengthFence.allocation 17
    let V : Nat → Option Bool := fun i =>
      if i=hole then none else if i=marker then some true else if i=p then some false
      else if i < S ∨ S < i ∧ i < S+z+2 then some false
      else if S+z+2 < i ∧ i < S+z+n.val+3 then some false
      else if S+z+n.val+3 < i ∧ i ≤ S+z+n.val+3+2^n.val then some true
      else if i=53 then some false else none
    let C := SuffixCap.Target.image V 53 (S-p)
    ∃ v, v ≤ 128*(n.val+(S-p)+1)*(53+5*(S-p)+n.val+9) ∧
      (AllArityCursor.machine 0).run ((2+(S-p)*(2*(53-p)+6))+v)
        (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount 17 B))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          ⟨Cursor.q 0 201,⟨54,by decide⟩,fun i => CappedWorkspace.Target.image C (S+z+2) n.val 53 (S-p) i.val⟩ := @AllArityWorkspace.Fixtures.workspace_false n
/-- Complete prepared COUNTED plus six-bank body for n0/1/2; not a raw accepted word. -/
theorem workspace_true (n : Fin 3) :
    let z := if n.val=0 then 0 else 1
    let hole := if n.val=0 then 7 else 9
    let marker := if n.val=0 then 8 else 10
    let p := 9+2*z+2^n.val
    let S := p+1
    let B := FixedRawLengthFence.allocation 17
    let V : Nat → Option Bool := fun i =>
      if i=hole then none else if i=marker then some true else if i=p then some true
      else if i < S ∨ S < i ∧ i < S+z+2 then some false
      else if S+z+2 < i ∧ i < S+z+n.val+3 then some false
      else if S+z+n.val+3 < i ∧ i ≤ S+z+n.val+3+2^n.val then some true
      else if i=53 then some false else none
    let C := SuffixCap.Target.image V 53 (S-p)
    ∃ v, v ≤ 128*(n.val+(S-p)+1)*(53+5*(S-p)+n.val+9) ∧
      (AllArityCursor.machine 0).run ((2+(S-p)*(2*(53-p)+6))+v)
        (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount 17 B))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          ⟨Cursor.q 0 201,⟨54,by decide⟩,fun i => CappedWorkspace.Target.image C (S+z+2) n.val 53 (S-p) i.val⟩ := by
  dsimp only
  obtain ⟨v,hv,done⟩ := setup (if n.val=0 then 7 else 9) (if n.val=0 then 8 else 10)
    (9+2*(if n.val=0 then 0 else 1)+2^n.val) (9+2*(if n.val=0 then 0 else 1)+2^n.val+1)
    (if n.val=0 then 0 else 1) n.val true (by fin_cases n <;> decide) (by fin_cases n <;> decide)
    rfl (by fin_cases n <;> decide) (by fin_cases n <;> decide)
  refine ⟨v,hv,?_⟩
  rw [UniformTM.run_add,AllArityCounted.Fixtures.counted_true n]
  exact done
theorem check_workspace_true (n : Fin 3) :
    let z := if n.val=0 then 0 else 1
    let hole := if n.val=0 then 7 else 9
    let marker := if n.val=0 then 8 else 10
    let p := 9+2*z+2^n.val
    let S := p+1
    let B := FixedRawLengthFence.allocation 17
    let V : Nat → Option Bool := fun i =>
      if i=hole then none else if i=marker then some true else if i=p then some true
      else if i < S ∨ S < i ∧ i < S+z+2 then some false
      else if S+z+2 < i ∧ i < S+z+n.val+3 then some false
      else if S+z+n.val+3 < i ∧ i ≤ S+z+n.val+3+2^n.val then some true
      else if i=53 then some false else none
    let C := SuffixCap.Target.image V 53 (S-p)
    ∃ v, v ≤ 128*(n.val+(S-p)+1)*(53+5*(S-p)+n.val+9) ∧
      (AllArityCursor.machine 0).run ((2+(S-p)*(2*(53-p)+6))+v)
        (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount 17 B))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
          ⟨Cursor.q 0 201,⟨54,by decide⟩,fun i => CappedWorkspace.Target.image C (S+z+2) n.val 53 (S-p) i.val⟩ := @AllArityWorkspace.Fixtures.workspace_true n
/-- Prepared EOF endpoint, including width0 adjacent delimiters, reused literally. -/
theorem eof_small (n : Fin 3) :
    let z := if n.val=0 then 0 else 1
    let S := if n.val=0 then 9 else 11
    let hole := if n.val=0 then 7 else 9
    let marker := if n.val=0 then 8 else 10
    let B := FixedRawLengthFence.allocation 17
    let V : Nat → Option Bool := fun i =>
      if i=hole then none else if i=marker then some true else if i=S-1 then some false
      else if i < S ∨ S < i ∧ i < S+z+2 then some false
      else if S+z+2 < i ∧ i < S+z+n.val+3 then some false
      else if S+z+n.val+3 < i ∧ i ≤ S+z+n.val+3+2^n.val then some true
      else if i=53 then some false else none
    (AllArityCursor.machine 0).run (z+n.val+5)
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 57,⟨S,by fin_cases n <;> decide⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.mReady 0 ⟨2,by decide⟩,⟨S+z+n.val+3,by fin_cases n <;> decide⟩,fun i => V i.val⟩ := @AllArityCounted.Fixtures.eof_small n
theorem check_eof_small (n : Fin 3) :
    let z := if n.val=0 then 0 else 1
    let S := if n.val=0 then 9 else 11
    let hole := if n.val=0 then 7 else 9
    let marker := if n.val=0 then 8 else 10
    let B := FixedRawLengthFence.allocation 17
    let V : Nat → Option Bool := fun i =>
      if i=hole then none else if i=marker then some true else if i=S-1 then some false
      else if i < S ∨ S < i ∧ i < S+z+2 then some false
      else if S+z+2 < i ∧ i < S+z+n.val+3 then some false
      else if S+z+n.val+3 < i ∧ i ≤ S+z+n.val+3+2^n.val then some true
      else if i=53 then some false else none
    (AllArityCursor.machine 0).run (z+n.val+5)
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 57,⟨S,by fin_cases n <;> decide⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.mReady 0 ⟨2,by decide⟩,⟨S+z+n.val+3,by fin_cases n <;> decide⟩,fun i => V i.val⟩ := @AllArityWorkspace.Fixtures.eof_small n
end AllArityWorkspace.Fixtures
#print axioms AllArityWorkspace.Fixtures.workspace_false
#print axioms AllArityWorkspace.Fixtures.check_workspace_false
#print axioms AllArityWorkspace.Fixtures.workspace_true
#print axioms AllArityWorkspace.Fixtures.check_workspace_true
#print axioms AllArityWorkspace.Fixtures.eof_small
#print axioms AllArityWorkspace.Fixtures.check_eof_small
