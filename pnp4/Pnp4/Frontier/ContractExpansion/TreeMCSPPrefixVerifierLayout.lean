import Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# Input-tape layout for the prefix-extension verifier Turing machine

Phase 6 (first brick) of the NP-verifier track — see `TM_VERIFIER_STRATEGY.md`.

The verifier TM reads `concatBitstring query cert`, where `query : Bitstring N` is the parsed
prefix-language instance and `cert : Bitstring (certificateLength N 1)` is the certificate.  This
module fixes the **data-independent** tape layout (the input length and the certificate / witness
region offsets) and proves the basic fit lemmas the per-phase TM programs will rely on.

No Turing machine is built here; this is layout arithmetic only (`Classical`-free).
-/

/-- Length of the verifier's input tape: the length-`N` query followed by the certificate of length
`certificateLength N 1 = N + 1`. -/
def prefixVerifierInputLen (N : Nat) : Nat :=
  N + Pnp3.ComplexityInterfaces.certificateLength N 1

/-- The input tape has length `2 N + 1`. -/
theorem prefixVerifierInputLen_eq (N : Nat) :
    prefixVerifierInputLen N = 2 * N + 1 := by
  unfold prefixVerifierInputLen
  simp only [Pnp3.ComplexityInterfaces.certificateLength, pow_one]
  omega

/-- The certificate region starts immediately after the length-`N` query. -/
def prefixVerifierCertStart (N : Nat) : Nat := N

/--
The witness prefix occupies the first `codec.witnessBits n` cells of the certificate region;
under the parser length convention (`N = treeMCSPPrefixM codec n`) it fits inside the input tape.
This is the on-tape counterpart of `extractWitness_eq`: the verifier can address the witness bits
without running past the input.
-/
theorem prefixVerifierWitnessRegion_within_input
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    (n N : Nat) (hM : N = treeMCSPPrefixM codec n) :
    prefixVerifierCertStart N + codec.witnessBits n ≤ prefixVerifierInputLen N := by
  unfold prefixVerifierCertStart prefixVerifierInputLen
  have h := witnessBits_le_certificateLength codec n N hM
  omega

end ContractExpansion
end Frontier
end Pnp4
