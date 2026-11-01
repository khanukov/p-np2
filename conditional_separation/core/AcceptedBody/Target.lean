import Body.Raw
import Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound

namespace AcceptedBody
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding

abbrev Parsed (k : Nat) := Sigma fun r : Nat =>
  PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
    (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
    (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)

/-- Time upper bound only; this does not change the literal run's tape allocation. -/
def deadline (R : Nat) : Nat := 132 * (R+1)^2

/-- Accepted-side semantic cap and the actual physical orbit. Small n, runtime
reads, comparison, malformed partition and verifier clock remain outside this target. -/
def AcceptedOrbit (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w = true →
    ∃ pr : Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      (3 ≤ pr.2.n → ∃ z T,
        2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z ∧
        pr.2.n < FixedRawLengthFence.capacity a m z ∧
        T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
        ∀ r, r < 2^pr.2.n →
          T+pr.2.n+2+Body.iterClock (List.replicate pr.2.n false) r ≤ deadline (pairLength a m) ∧
          let e := Body.rawMachine.run (T+pr.2.n+2+Body.iterClock (List.replicate pr.2.n false) r)
            (initialConfig Body.rawMachine (FixedRawLengthFence.allocation (pairLength a m))
              (encodePair x w))
          e.state = FixedRawLengthFence.prefixed.seqRight Body.machine (Body.q 2) ∧
          e.head.val = a+m+2+z+pr.2.n+1 ∧
          Body.Target.Span e.tape (a+m+2+z) (Body.iterBits (List.replicate pr.2.n false) r) ∧
          ∀ (i : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))))
            (_lo : 8+2*z+1 ≤ i.val) (hi : i.val < a+m),
            e.tape i = some (Fin.append x w ⟨i.val,hi⟩))
end AcceptedBody
