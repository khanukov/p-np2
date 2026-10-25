import VirtualFinalClosure.Finite
namespace VirtualFinalClosure.ConfigFields
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
private theorem sequential (A B : UniformTM) {N C : Nat}
    (c : Config B.stateCount N C) :
    (A.seqEmbedRight B c).state.val=A.stateCount+c.state.val := by rfl
private theorem extension {states N C B : Nat} (h : C≤B) (c : Config states N C) :
    (IngressAllocation.extendConfig h c).state.val=c.state.val := by rfl
private theorem total (k : Nat) {N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B) :
    (TotalIngressClosure.config k c).state.val=10+c.state.val := by
  exact sequential FixedPairParser.machine (BodyIngress.machine k) c
private theorem guarded (k : Nat) {N B : Nat}
    (c : Config (TotalIngressClosure.machine k).stateCount N B) :
    (CertificateGuardClosure.config k c).state.val=77+c.state.val := by
  have inner:=sequential CertificateGuardClosure.guard (TotalIngressClosure.machine k) c
  have outer:=sequential FixedPairParser.machine
    (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
    (CertificateGuardClosure.guard.seqEmbedRight (TotalIngressClosure.machine k) c)
  change _=77+c.state.val
  rw [show (CertificateGuardClosure.config k c).state.val=
    10+(CertificateGuardClosure.guard.seqEmbedRight (TotalIngressClosure.machine k) c).state.val from outer,inner]
  change 10+(67+c.state.val)=77+c.state.val
  omega
#print axioms sequential
#print axioms extension
#print axioms total
#print axioms guarded
end VirtualFinalClosure.ConfigFields
