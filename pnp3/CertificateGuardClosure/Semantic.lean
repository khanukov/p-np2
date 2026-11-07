import CertificateGuardClosure.Joint
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
/-- The exact original length guard; this semantic lemma is NOT a physical guard. -/
theorem wrong_length {a m : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    (h : m ≠ a+1) : PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  have bad : m ≠ Pnp3.ComplexityInterfaces.certificateLength a 1 := by
    simpa [Pnp3.ComplexityInterfaces.certificateLength] using h
  simp [PartAEndpoint.thresholdContentWitnessRelation,PartAEndpoint.contentWitnessRelation,bad]
theorem wrong_length_mirror :
    ∀ {a m : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m),
      m ≠ a+1 → PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  intro a m k x w h
  exact wrong_length k x w h
/-- Genuine same-language existential reduction to the exact original certificate size. -/
theorem exists_canonical (k a : Nat) (x : Bitstring a) :
    (∃ m : Nat, ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) ↔
    ∃ w : Bitstring (a+1),PartAEndpoint.thresholdContentWitnessRelation k a (a+1) x w=true := by
  constructor
  · rintro ⟨m,w,hw⟩
    have hm : m=a+1 := by
      by_contra bad
      have hf:=wrong_length k x w bad
      simp [hf] at hw
    subst m
    exact ⟨w,hw⟩
  · rintro ⟨w,hw⟩
    exact ⟨a+1,w,hw⟩
theorem exists_canonical_mirror :
    ∀ (k a : Nat) (x : Bitstring a),
    (∃ m : Nat, ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) ↔
    ∃ w : Bitstring (a+1),PartAEndpoint.thresholdContentWitnessRelation k a (a+1) x w=true := by
  intro k a x
  exact exists_canonical k a x
#print axioms CertificateGuardClosure.wrong_length
#print axioms CertificateGuardClosure.wrong_length_mirror
#print axioms CertificateGuardClosure.exists_canonical
#print axioms CertificateGuardClosure.exists_canonical_mirror
end CertificateGuardClosure
