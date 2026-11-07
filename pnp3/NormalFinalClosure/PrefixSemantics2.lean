import NormalFinalClosure.PrefixLoop2
import NormalFinalClosure.BESemantics2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,leaves) in [
    (`NormalFinalClosure.IndexImage2,["sourceMode"]),
    (`NormalFinalClosure.PrefixCode2,["activeCode"]),
    (`NormalFinalClosure.PrefixDigit2,["nextRecord"]),
    (`NormalFinalClosure.PrefixLoop2,["prefixGood","prefixRecords"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `NormalFinalClosure) leaf
      let some ci:=e.find? name | throwError "Missing original-prefix semantic API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing original-prefix semantic owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong original-prefix semantic owner"
      logInfo m!"native-prefix-original-bytes-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem mode_one_iff {S : Nat} (source : Fin S → Bool) (offset : Nat) :
    (sourceMode source (min offset S)).val=1 ↔ padRead source offset=true := by
  by_cases physical:offset < S
  · rw [show min offset S=offset by omega]
    simp only [sourceMode,padRead,dif_pos physical]
    cases b:source ⟨offset,physical⟩ <;> decide
  · rw [show min offset S=S by omega]
    simp only [sourceMode,Nat.lt_irrefl,padRead,dif_neg physical]
    simp only [dite_false]
    decide
private theorem activeCode_original {S : Nat} (source : Fin S → Bool) (offset : Nat) :
    activeCode (sourceMode source (min offset S))=if padRead source offset then 2 else 1 := by
  dsimp only [activeCode]
  simp only [mode_one_iff]
private def windowBits {S : Nat} (source : Fin S → Bool) (offset : Nat) : Nat → List Bool
  | 0=>[]
  | v+1=>padRead source offset::windowBits source (offset+1) v
private def encodeBits (bits : List Bool) : List Nat := bits.map (fun bit=>if bit then 2 else 1)
private theorem windowBits_length {S : Nat} (source : Fin S → Bool) (v offset : Nat) :
    (windowBits source offset v).length=v := by
  induction v generalizing offset with
  | zero=>rfl
  | succ v ih=>simp only [windowBits,List.length_cons,ih]
/-- Exact ORIGINAL inactive padding, including partially physical fields and
virtual low suffix zeros. No extra physical support hypothesis is used. -/
private theorem prefixGood_original {S : Nat} (source : Fin S → Bool) (v offset index : Nat)
    (cap:index ≤ v) :
    prefixGood source (min offset S) v index ↔
      ∀ j,index ≤ j → j < v → padRead source (offset+j)=false := by
  induction v generalizing offset index with
  | zero=>
    constructor
    · intro _ j _ hj;omega
    · intro _;trivial
  | succ v ih=>
    rw [prefixGood,show min (min offset S+1) S=min (offset+1) S by omega]
    cases index with
    | zero=>
      simp only [Nat.zero_sub,mode_one_iff]
      constructor
      · rintro ⟨head,tail⟩ j _ hj
        cases j with
        | zero=>
          have bit:padRead source offset=false:=by
            cases b:padRead source offset
            · rfl
            · exact False.elim (head ⟨trivial,b⟩)
          simpa only [Nat.add_zero] using bit
        | succ j=>
          have bits:=(ih (offset+1) 0 (by omega)).mp tail j (by omega) (by omega)
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bits
      · intro zeros
        refine ⟨?_,(ih (offset+1) 0 (by omega)).mpr ?_⟩
        · rintro ⟨_,one⟩
          have zero:=zeros 0 (by omega) (by omega)
          simp only [Nat.add_zero,one] at zero
          cases zero
        · intro j _ hj
          have bit:=zeros (j+1) (by omega) (by omega)
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bit
    | succ index=>
      simp only [show index+1≠0 by omega,false_and,not_false_eq_true,true_and,Nat.add_sub_cancel]
      rw [ih (offset+1) index (by omega)]
      constructor
      · intro zeros j lo hj
        obtain ⟨j,eq⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
        subst eq
        have bit:=zeros j (by omega) (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bit
      · intro zeros j lo hj
        have bit:=zeros (j+1) (by omega) (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bit
/-- The native buffer is exactly all ORIGINAL active bytes (not just decoder's
consumed syntax), followed by checked zero records for inactive padding. -/
private theorem prefixRecords_original {S : Nat} (source : Fin S → Bool) (v offset index : Nat)
    (cap:index ≤ v) :
    prefixRecords source (min offset S) v index=
      encodeBits (windowBits source offset index)++List.replicate (v-index) 0 := by
  induction v generalizing offset index with
  | zero=>
    have eq:index=0:=by omega
    subst index
    rfl
  | succ v ih=>
    rw [prefixRecords,show min (min offset S+1) S=min (offset+1) S by omega]
    cases index with
    | zero=>
      rw [ih (offset+1) 0 (by omega)]
      simp only [nextRecord,ite_true,windowBits,encodeBits,List.map_nil,List.nil_append,
        Nat.sub_zero,List.replicate_succ]
    | succ index=>
      rw [show index+1-1=index by omega,ih (offset+1) index (by omega)]
      simp only [nextRecord,show index+1≠0 by omega,if_false,activeCode_original,
        windowBits,encodeBits,List.map_cons,List.cons_append,Nat.add_sub_add_right]
end NormalFinalClosure
