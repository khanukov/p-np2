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

/-!
## Reading the concatenated verifier input

The verifier TM is run on `concatBitstring query cert`; `initialConfig` loads that string onto the
tape, so reading tape cell `j` returns `query j` for `j < N` and `cert (j - N)` for `N ≤ j`.  These
projection lemmas characterize `concatBitstring` bit-by-bit.  Because `concatBitstring` is
`noncomputable` (its right half is defined via `Classical.choose`), the projections are *not*
definitional and must be proved; they are the foundation of any future
`accepts M (concatBitstring x w) = …` reasoning.
-/

/-- On the left block, the concatenation reads as the instance `x`. -/
theorem concatBitstring_left {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (i : Fin (n + m)) (h : (i : Nat) < n) :
    Pnp3.ComplexityInterfaces.concatBitstring x w i = x ⟨(i : Nat), h⟩ := by
  unfold Pnp3.ComplexityInterfaces.concatBitstring
  rw [dif_pos h]

/-- On the right block, the concatenation reads as the certificate `w`. -/
theorem concatBitstring_right {n m : Nat}
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (i : Fin (n + m)) (h : n ≤ (i : Nat)) :
    Pnp3.ComplexityInterfaces.concatBitstring x w i
      = w ⟨(i : Nat) - n, by omega⟩ := by
  have hnlt : ¬ (i : Nat) < n := by omega
  unfold Pnp3.ComplexityInterfaces.concatBitstring
  rw [dif_neg hnlt]
  refine congrArg w (Fin.ext ?_)
  show Classical.choose (Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnlt)) = (i : Nat) - n
  have hspec := Classical.choose_spec (Nat.exists_eq_add_of_le (Nat.le_of_not_gt hnlt))
  omega

/-!
### Tape reading at the start of a verifier run

Composing the existing `@[simp]` lemma `TM.initial_tape_input` with the projections above: when any
Turing machine `M` is started on `concatBitstring x w`, a tape cell in the left block reads the
instance `x` and a cell in the right block reads the certificate `w`.  These are the exact statements
a per-phase verifier program will use to relate a read bit back to `query` / `cert`.
-/

/-- A left-block tape cell, at the start of a run on `concatBitstring x w`, reads the instance. -/
theorem verifierTape_left {n m : Nat} (M : Pnp3.Internal.PsubsetPpoly.TM)
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) (hj : (j : Nat) < n) :
    (M.initialConfig (Pnp3.ComplexityInterfaces.concatBitstring x w)).tape j
      = x ⟨(j : Nat), hj⟩ := by
  have hlt : (j : Nat) < n + m := by omega
  rw [Pnp3.Internal.PsubsetPpoly.TM.initial_tape_input (M := M)
        (Pnp3.ComplexityInterfaces.concatBitstring x w) hlt]
  exact concatBitstring_left x w ⟨(j : Nat), hlt⟩ hj

/-- A right-block tape cell, at the start of a run on `concatBitstring x w`, reads the certificate. -/
theorem verifierTape_right {n m : Nat} (M : Pnp3.Internal.PsubsetPpoly.TM)
    (x : Pnp3.ComplexityInterfaces.Bitstring n) (w : Pnp3.ComplexityInterfaces.Bitstring m)
    (j : Fin (M.tapeLength (n + m))) (hj1 : n ≤ (j : Nat)) (hj2 : (j : Nat) < n + m) :
    (M.initialConfig (Pnp3.ComplexityInterfaces.concatBitstring x w)).tape j
      = w ⟨(j : Nat) - n, by omega⟩ := by
  rw [Pnp3.Internal.PsubsetPpoly.TM.initial_tape_input (M := M)
        (Pnp3.ComplexityInterfaces.concatBitstring x w) hj2]
  exact concatBitstring_right x w ⟨(j : Nat), hj2⟩ hj1

end ContractExpansion
end Frontier
end Pnp4
