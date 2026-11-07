import NormalFinalClosure.CompareLoop2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,leaves) in [
    (`NormalFinalClosure.CompareLoop2,["bitsAgree"]),
    (`NormalFinalClosure.PrefixSemantics2,["windowBits"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) `NormalFinalClosure) leaf
      let some ci:=e.find? name | throwError "Missing complete original-window semantic API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing original-window semantic owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong original-window semantic owner"
      logInfo m!"complete-original-window-comparison-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
/-- Comparison is on the complete original witness window, regardless of where
the decoder stopped. No serializer replacement or ignored-tail zero test. -/
private theorem matches_window_original {S : Nat} (source : Fin S → Bool) (width prefixAt witnessAt : Nat) :
    bitsAgree source witnessAt (windowBits source prefixAt width) ↔
      ∀ j,j < width → padRead source (prefixAt+j)=padRead source (witnessAt+j) := by
  induction width generalizing prefixAt witnessAt with
  | zero=>
    constructor
    · intro _ j hj;omega
    · intro _;trivial
  | succ width ih=>
    rw [windowBits,bitsAgree,ih]
    constructor
    · rintro ⟨head,tail⟩ j hj
      cases j with
      | zero=>simpa only [Nat.add_zero] using head
      | succ j=>
        have h:=tail j (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · intro agree
      refine ⟨by simpa only [Nat.add_zero] using agree 0 (by omega),?_⟩
      intro j hj
      have h:=agree (j+1) (by omega)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
end NormalFinalClosure
