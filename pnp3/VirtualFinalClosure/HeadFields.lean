import VirtualFinalClosure.ConfigFields
namespace VirtualFinalClosure.HeadFields
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
private theorem sequential (A B : UniformTM) {N C : Nat} (c : Config B.stateCount N C) :
    (A.seqEmbedRight B c).head.val=c.head.val := by dsimp only [UniformTM.seqEmbedRight]
private theorem extension {states N C B : Nat} (h : C≤B) (c : Config states N C) :
    (IngressAllocation.extendConfig h c).head.val=c.head.val := by
  dsimp only [IngressAllocation.extendConfig,FixedPairParser.tapeEmbed]
private theorem total (k : Nat) {N B : Nat} (c : Config (BodyIngress.machine k).stateCount N B) :
    (TotalIngressClosure.config k c).head.val=c.head.val := by
  dsimp only [TotalIngressClosure.config,UniformTM.seqEmbedRight]
private theorem guarded (k : Nat) {N B : Nat} (c : Config (TotalIngressClosure.machine k).stateCount N B) :
    (CertificateGuardClosure.config k c).head.val=c.head.val := by
  dsimp only [CertificateGuardClosure.config,UniformTM.seqEmbedRight]
private theorem included (k : Nat) {N B : Nat} (f : Fin 144)
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) :
    (config k f c).head.val=c.head.val := by dsimp only [config]
#print axioms sequential
#print axioms extension
#print axioms total
#print axioms guarded
#print axioms included
end VirtualFinalClosure.HeadFields
