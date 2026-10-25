import VirtualFinalClosure.ZeroMeaning
namespace VirtualFinalClosure.ReverseSourceMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let found:=(←getEnv).constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.ZeroMeaning." && name.toString.endsWith ".VirtualFinalClosure.ZeroMeaning.physical_zero"
  match found with
  | [(name,.thmInfo ci)]=>
    logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `physicalZero name::st.openDecls}
  | _=>throwError "Nonunique physical reverse-source interpretation"
private theorem zero_iff {S : Nat} (word : Bitstring S) (p : Nat) (I : Nat → Option Bool)
    (source : ∀ i,p ≤ i → ∀ hi:i < S,I i=some (word ⟨i,hi⟩)) :
    (∀ j,j < S-p → (I (S-1-j)).getD false=false) ↔
      ∀ i,p ≤ i → i < S → padRead word i=false:=by
  constructor
  · exact physicalZero word I source
  · intro zero j hj
    have inside : S-1-j < S:=by omega
    have lo : p ≤ S-1-j:=by omega
    rw [source (S-1-j) lo inside]
    have bit:=zero (S-1-j) lo inside
    dsimp only [padRead] at bit
    rw [dif_pos inside] at bit
    exact bit
#print axioms zero_iff
end VirtualFinalClosure.ReverseSourceMeaning
