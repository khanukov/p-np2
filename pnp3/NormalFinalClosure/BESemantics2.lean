import NormalFinalClosure.BELoop2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,leaves) in [
    (`NormalFinalClosure.IndexImage2,["sourceMode"]),
    (`NormalFinalClosure.BEBit2,["modeDigit"]),
    (`NormalFinalClosure.BELoop2,["indexValue"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `NormalFinalClosure) leaf
      let some ci:=e.find? name | throwError "Missing actual BE semantic interface"
      let some i:=e.getModuleIdxFor? name | throwError "Missing actual BE semantic owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong BE semantic owner"
      logInfo m!"native-BE-original-reader-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem source_digit {S : Nat} (source : Fin S → Bool) (offset : Nat) :
    modeDigit (sourceMode source (min offset S))=if padRead source offset then 1 else 0 := by
  by_cases physical:offset < S
  · rw [show min offset S=offset by omega]
    simp only [sourceMode,padRead,dif_pos physical]
    cases b:source ⟨offset,physical⟩ <;> rfl
  · rw [show min offset S=S by omega]
    simp only [sourceMode,Nat.lt_irrefl,padRead,dif_neg physical,modeDigit]
    rfl
/-- A mathematical specification used only in proofs. Exact high-bit/virtual
low-zero orientation of the ORIGINAL BE field is retained. -/
private def wordValue {S : Nat} (source : Fin S → Bool) (offset : Nat) : Nat → Nat
  | 0=>0
  | v+1=>(if padRead source offset then 2^v else 0)+wordValue source (offset+1) v
private theorem indexValue_original {S : Nat} (source : Fin S → Bool) (v offset acc : Nat) :
    indexValue source (min offset S) v acc=acc*2^v+wordValue source offset v := by
  induction v generalizing offset acc with
  | zero=>simp only [indexValue,wordValue,pow_zero,Nat.mul_one,Nat.add_zero]
  | succ v ih=>
    rw [indexValue,show min (min offset S+1) S=min (offset+1) S by omega,ih,source_digit,wordValue]
    rw [pow_succ]
    cases b:padRead source offset <;> simp only [ite_true,ite_false,Bool.false_eq_true]
    all_goals ring
private theorem read_wordValue {S : Nat} (source : Fin S → Bool) (v offset logical : Nat)
    (fit:offset+v ≤ logical) :
    readNatBE (padWord source logical) offset v=some (wordValue source offset v) := by
  induction v generalizing offset with
  | zero=>rfl
  | succ v ih=>
    rw [readNatBE,show readBit? (padWord source logical) offset=some (padRead source offset) by
      rw [readBit?,dif_pos (by omega)];rfl,
      ih (offset+1) (by omega)]
    rfl
private theorem read_indexValue {S : Nat} (source : Fin S → Bool) (v offset logical : Nat)
    (fit:offset+v ≤ logical) :
    readNatBE (padWord source logical) offset v=some (indexValue source (min offset S) v 0) := by
  rw [indexValue_original,Nat.zero_mul,Nat.zero_add]
  exact read_wordValue source v offset logical fit
end NormalFinalClosure
