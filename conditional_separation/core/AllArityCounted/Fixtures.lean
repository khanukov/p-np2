import AllArityCounted.Runtime
import Lean
namespace AllArityCounted.Fixtures
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
attribute [local irreducible] UniformTM.run
private def layout (hole marker p S z n : Nat) (b : Bool) : Nat → Option Bool := fun i =>
  if i=hole then none else if i=marker then some true else if i=p then some b
  else if i < S ∨ S < i ∧ i < S+z+2 then some false
  else if S+z+2 < i ∧ i < S+z+n+3 then some false
  else if S+z+n+3 < i ∧ i ≤ S+z+n+3+2^n then some true
  else if i=53 then some false else none
private theorem fixed_fit (i : Nat) (hi : i < 53) :
    i < tapeLength 17 (FixedRawLengthFence.allocation 17) := hi.trans (by decide)
private theorem arena_lt (S z n Q : Nat) (room : S+z+n+3+Q < 53) : S < 53 := by omega
private theorem counted_layout (hole marker p S z n : Nat) (b : Bool)
    (hh : hole < p) (hm : marker < p) (unit : p+1=S) (room : S+z+n+3+2^n < 53) :
    let B := FixedRawLengthFence.allocation 17
    let V := layout hole marker p S z n b
    (AllArityCursor.machine 0).run (2+(S-p)*(2*(53-p)+6))
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨p,fixed_fit p (lt_trans (by omega) (arena_lt S z n (2^n) room))⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.rReady 0,⟨S,fixed_fit S (arena_lt S z n (2^n) room)⟩,
          fun i => SuffixCap.Target.image V 53 (S-p) i.val⟩ := by
  let B := FixedRawLengthFence.allocation 17
  let V := layout hole marker p S z n b
  have paid : 0 < 2^n := by positivity
  have big : 56 < tapeLength 17 B := by decide
  have source (i : Nat) (lo : p ≤ i) (hi : i < S) : ∃ v, V i=some v := by
    have e : i=p := by omega
    subst i
    exact ⟨b,by simp [V,layout,show p≠hole by omega,show p≠marker by omega]⟩
  have eof : V S=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have reg (i : Nat) (lo : S < i) (hi : i < S+z+2) : V i=some false := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (Or.inr ⟨lo,hi⟩)]
  have sep : V (S+z+2)=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have assn (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : ∃ v, V i=some v := by
    refine ⟨false,?_⟩
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨lo,hi⟩]
  have right : V (S+z+n+3)=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have marks (i : Nat) (lo : S+z+n+3 < i) (hi : i ≤ S+z+n+3+2^n) : V i=some true := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨lo,hi⟩]
  have gap (i : Nat) (lo : S+z+n+3+2^n < i) (hi : i < 53) : V i=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have fence : V 53=some false := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have fresh (i : Nat) (lo : 53 < i) (hi : i ≤ 53+(S-p)+2) : V i=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have kernel := SuffixCap.counted 0 17 B p S z n (2^n) 53 V (by omega) (by omega)
    paid room source eof reg sep assn right marks gap fence fresh (by omega)
  change (SmallIngress.producer.seq (Cursor.machine 0)).run _ _=_
  rw [UniformTM.seq_run_right]
  exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)) kernel.1
private theorem eof_layout (hole marker S z n : Nat) (hh : hole < S) (hm : marker < S)
    (room : S+z+n+3+2^n < 53) :
    let B := FixedRawLengthFence.allocation 17
    let V := layout hole marker (S-1) S z n false
    (AllArityCursor.machine 0).run (z+n+5)
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 57,⟨S,fixed_fit S (arena_lt S z n (2^n) room)⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.mReady 0 ⟨2,by decide⟩,
          ⟨S+z+n+3,fixed_fit _ (lt_of_le_of_lt (Nat.le_add_right _ _) room)⟩,fun i => V i.val⟩ := by
  let B := FixedRawLengthFence.allocation 17
  let V := layout hole marker (S-1) S z n false
  have paid : 0 < 2^n := by positivity
  have big : 56 < tapeLength 17 B := by decide
  have eof : V S=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have reg (i : Nat) (lo : S < i) (hi : i < S+z+2) : V i=some false := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (Or.inr ⟨lo,hi⟩)]
  have sep : V (S+z+2)=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have assn (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : ∃ v, V i=some v := by
    refine ⟨false,?_⟩
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨lo,hi⟩]
  have right : V (S+z+n+3)=none := by
    dsimp only [V,layout]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have body := AllArityCounted.eof_body (N := 17) (B := B) 0 V S z n (by omega) eof reg sep assn right
  change (SmallIngress.producer.seq (Cursor.machine 0)).run _ _=_
  rw [UniformTM.seq_run_right]
  exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)) body
/-- Prepared full COUNTED body for all n0/1/2 geometries; not an accepted raw example. -/
theorem counted_false (n : Fin 3) :
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
    (AllArityCursor.machine 0).run (2+(S-p)*(2*(53-p)+6))
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.rReady 0,⟨S,by fin_cases n <;> decide⟩,
          fun i => SuffixCap.Target.image V 53 (S-p) i.val⟩ := by
  dsimp only
  apply counted_layout
  all_goals fin_cases n <;> decide
/-- Prepared full COUNTED body for all n0/1/2 geometries; not an accepted raw example. -/
theorem counted_true (n : Fin 3) :
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
    (AllArityCursor.machine 0).run (2+(S-p)*(2*(53-p)+6))
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.rReady 0,⟨S,by fin_cases n <;> decide⟩,
          fun i => SuffixCap.Target.image V 53 (S-p) i.val⟩ := by
  dsimp only
  apply counted_layout
  all_goals fin_cases n <;> decide
/-- Prepared exact EOF endpoint for canonical small widths, including adjacent blanks at n0. -/
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
        ⟨Cursor.mReady 0 ⟨2,by decide⟩,⟨S+z+n.val+3,by fin_cases n <;> decide⟩,fun i => V i.val⟩ := by
  dsimp only
  apply eof_layout
  all_goals fin_cases n <;> decide
theorem check_counted_false (n : Fin 3) :
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
    (AllArityCursor.machine 0).run (2+(S-p)*(2*(53-p)+6))
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.rReady 0,⟨S,by fin_cases n <;> decide⟩,
          fun i => SuffixCap.Target.image V 53 (S-p) i.val⟩ := @AllArityCounted.Fixtures.counted_false n
theorem check_counted_true (n : Fin 3) :
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
    (AllArityCursor.machine 0).run (2+(S-p)*(2*(53-p)+6))
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨p,by fin_cases n <;> decide⟩,fun i => V i.val⟩ :
          Config (Cursor.machine 0).stateCount 17 B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.rReady 0,⟨S,by fin_cases n <;> decide⟩,
          fun i => SuffixCap.Target.image V 53 (S-p) i.val⟩ := @AllArityCounted.Fixtures.counted_true n
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
        ⟨Cursor.mReady 0 ⟨2,by decide⟩,⟨S+z+n.val+3,by fin_cases n <;> decide⟩,fun i => V i.val⟩ := @AllArityCounted.Fixtures.eof_small n
end AllArityCounted.Fixtures
#print axioms AllArityCounted.Fixtures.counted_false
#print axioms AllArityCounted.Fixtures.check_counted_false
#print axioms AllArityCounted.Fixtures.counted_true
#print axioms AllArityCounted.Fixtures.check_counted_true
#print axioms AllArityCounted.Fixtures.eof_small
#print axioms AllArityCounted.Fixtures.check_eof_small
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "AllArityCounted." then logInfo m!"surface|{n}"
    if (e.getModuleIdxFor? n).isNone && !n.toString.startsWith "_private." then logInfo m!"owned|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
