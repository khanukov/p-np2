import VirtualFinalClosure.GuardAddresses
import Pnp4.Frontier.ContractExpansion.FixedContentTagGateCorrect
namespace VirtualFinalClosure.GuardTagMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
set_option autoImplicit false
private theorem read_congr {A B : Nat} (x : PrefixBitVec A) (y : PrefixBitVec B) (offset width : Nat)
    (same : ∀ j,j < width → readBit? x (offset+j)=readBit? y (offset+j)) :
    readNatBE x offset width=readNatBE y offset width := by
  induction width generalizing offset with
  | zero=>rfl
  | succ width ih=>
    have first : readBit? x offset=readBit? y offset:=by simpa only [Nat.add_zero] using same 0 (by omega)
    rw [readNatBE,readNatBE,first]
    have tail:=ih (offset+1) (by intro j hj;simpa only [Nat.add_assoc,Nat.add_comm 1 j] using same (j+1) (by omega))
    rw [tail]
private theorem tag_read {S : Nat} (word : Bitstring S) (M : Nat) (room : tagLen ≤ M)
    (tag : FixedContentTagGate.tagMatches word=true) :
    readNatBE (padWord word M) 0 tagLen=some treePrefixTag := by
  let expected : PrefixBitVec 8:=fun j=>natBitBE treePrefixTag tagLen j
  have same : readNatBE (padWord word M) 0 8=readNatBE expected 0 8 := by
    apply read_congr
    intro j hj
    have physical:=(fixedTagMatches_iff word).mp tag ⟨j,hj⟩
    dsimp only [FixedContentTagGate.physicalSymbol] at physical
    have jm : j < M:=by change 8 ≤ M at room;omega
    dsimp only [readBit?]
    rw [dif_pos (by omega : 0+j < M),dif_pos (by omega : 0+j < 8)]
    apply congrArg some
    simp only [padWord,expected,Nat.zero_add]
    by_cases js : j < S
    · rw [dif_pos js] at physical
      have bit:=Option.some.inj physical
      dsimp only [padRead]
      rw [dif_pos js]
      exact bit
    · rw [dif_neg js] at physical
      cases physical
  have exactTag : readNatBE expected 0 8=some treePrefixTag:=by decide
  exact same.trans exactTag
#print axioms read_congr
#print axioms tag_read
end VirtualFinalClosure.GuardTagMeaning
