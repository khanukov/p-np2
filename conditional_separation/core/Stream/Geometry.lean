import Stream.Target
import ConnectedRead.Closure
namespace Stream
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding

/-- The unused interval and its fence are derived from the real countdown tape,
then framed through actual unary installation. No clean-scratch premise. -/
theorem raw_budget_cells {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (room : n < FixedRawLengthFence.capacity a m z) :
    a+m+z+n+3 < FixedRawLengthFence.fencePos (pairLength a m) ∧
    (∀ i : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      a+m+z+n+3 ≤ i.val → i.val < FixedRawLengthFence.fencePos (pairLength a m) →
      Body.installedTape (FixedRawLengthFence.countdownTape
        (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (a+m+z+2) n i=none) ∧
    ∃ hf : FixedRawLengthFence.fencePos (pairLength a m) <
        tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
      Body.installedTape (FixedRawLengthFence.countdownTape
        (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (a+m+z+2) n
          ⟨FixedRawLengthFence.fencePos (pairLength a m),hf⟩=some false := by
  have resource := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma resource (Nat.le_of_lt room)
  have support := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  have geo : a+m+3+z+FixedRawLengthFence.capacity a m z=FixedRawLengthFence.fencePos (pairLength a m) := by
    simp only [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,pairLength] at *; omega
  have fit : FixedRawLengthFence.fencePos (pairLength a m) <
      tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) := by
    simp only [FixedRawLengthFence.fencePos,tapeLength] at *; omega
  refine ⟨by omega,?_,fit,?_⟩
  · intro i lo hi
    rw [Body.installedTape,if_neg (by omega)]
    exact cells.2.2.2.2.1 i (by omega) hi
  · rw [Body.installedTape,if_neg (by change ¬ (a+m+z+2 < FixedRawLengthFence.fencePos (pairLength a m) ∧ FixedRawLengthFence.fencePos (pairLength a m) < a+m+z+2+n+1); omega)]
    exact cells.2.2.2.2.2 _ rfl

/-- Nat subtraction and all delimiter offsets are explicit. This gives enough
physical tally cells for accepted rows, not a false-content verdict. -/
theorem accepted_budget {a m z n : Nat} (shape : m=a+1) (hz : z≤a+m) (hn : n≤a+m) :
    a+m ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1 := by
  simp only [FixedRawLengthFence.fencePos,pairLength]
  omega

/-- The exact relation discharges shape and row support for the SAME parsed
parameter, without interpreting a work exit as content acceptance. -/
theorem accepted_rows_fit (k : Nat) {a m z : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 := by
  have shape : m=a+1 := by
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at accepted
    split at accepted
    · rename_i h
      simpa [Pnp3.ComplexityInterfaces.certificateLength] using h
    · contradiction
  obtain ⟨pr',parsed',table,_⟩ := AcceptedBody.exact k x w accepted
  have eq : pr'=pr := Option.some.inj (parsed'.symm.trans parsed)
  subst pr'
  have small : pr.2.n≤a+m := by
    have h := Nat.lt_two_pow_self (n := pr.2.n)
    change 2^pr.2.n≤a+m at table
    omega
  have support := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  exact table.trans (accepted_budget shape (by omega) small)
end Stream
