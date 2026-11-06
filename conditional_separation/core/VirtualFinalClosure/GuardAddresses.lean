import VirtualFinalClosure.GuardValue
namespace VirtualFinalClosure.GuardAddresses
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds
set_option autoImplicit false
/-- Authoritative codec width equals the spec arithmetic physically computed
by the unchanged Cursor rows. Neither quantity is a transition operand. -/
private theorem width (k n : Nat) :
    (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n=Cursor.Target.W k n:=by
  rfl
private theorem index_width (k n : Nat) :
    idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n=bitLength (Cursor.Target.W k n):=by
  rfl
/-- SAME actual decoded gamma header fixes the full original content address,
including BOTH bitLength W and W. This is not a runtime installed address. -/
private theorem address {S n z : Nat} (k : Nat) (word : Bitstring S)
    (header : contentHeader? word=some (n,2*z+1)) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n=Cursor.Target.M k n z:=by
  have gamma:=contentHeader?_consumed_eq_gammaLen word header
  dsimp only [treeMCSPPrefixM]
  rw [←gamma,width k n,index_width k n]
  change 8+(2*z+1)+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n=
    9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n
  omega
private theorem index_start (n z : Nat) :
    tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n=9+2*z+2^n:=by
  change 8+(2*z+1)+2^n=9+2*z+2^n
  omega
#print axioms width
#print axioms index_width
#print axioms address
#print axioms index_start
end VirtualFinalClosure.GuardAddresses
