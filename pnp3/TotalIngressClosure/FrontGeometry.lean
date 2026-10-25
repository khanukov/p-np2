import TotalIngressClosure.Header
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
private theorem capacity_large {a m z : Nat} (x:Bitstring a) (w:Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    3 < FixedRawLengthFence.capacity a m z:=by
  have support:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  dsimp only [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,pairLength]
  omega
private theorem capacity_wide {a m n consumed z : Nat} (x:Bitstring a) (w:Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap:FixedRawLengthFence.capacity a m z ≤ n) : 2 ≤ z:=by
  obtain ⟨z',other,_len,_lower,upper,_borrow,_digits,_high⟩:=decremented_register_digits x w header
  have equal:z'=z:=Option.some.inj (other.symm.trans gamma)
  subst z'
  have big:=capacity_large x w gamma
  by_contra no
  have short:2^(z+1) ≤ (2:Nat)^2:=Nat.pow_le_pow_right (by decide :0 < (2:Nat)) (by omega)
  norm_num at short
  omega
private theorem missing_first_shape {a m z : Nat} (x:Bitstring a) (w:Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (short:¬(z=0 ∨ 9+z < a+m)) : 0 < z ∧ a+m=9+z:=by
  have support:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  omega
end TotalIngressClosure
