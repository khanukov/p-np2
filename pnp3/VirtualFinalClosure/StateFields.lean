import VirtualFinalClosure.ConfigFields
namespace VirtualFinalClosure.StateFields
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
private theorem sequential (A B : UniformTM) (q : Fin B.stateCount) :
    (A.seqRight B q).val=A.stateCount+q.val := by dsimp only [UniformTM.seqRight]
private theorem virtual_old (k : Nat) (q : Fin (IngressRepair.machine k).stateCount) :
    (VirtualLeaf.embed k q).val=q.val := by dsimp only [VirtualLeaf.embed]
private theorem carry_old (k : Nat) (q : Fin (CanonicalLeaf.machine k).stateCount) :
    (CarryWindow.embed k q).val=q.val := by dsimp only [CarryWindow.embed]
private theorem body_old (k : Nat) (q : Fin (CarryWindow.machine k).stateCount) :
    (BodyIngress.old k q).val=q.val := by dsimp only [BodyIngress.old]
private theorem total_old (k : Nat) (q : Fin (BodyIngress.machine k).stateCount) :
    (TotalIngressClosure.old k q).val=10+q.val := sequential FixedPairParser.machine (BodyIngress.machine k) q
private theorem guarded_old (k : Nat) (q : Fin (TotalIngressClosure.machine k).stateCount) :
    (CertificateGuardClosure.old k q).val=77+q.val := by
  have inner:=sequential CertificateGuardClosure.guard (TotalIngressClosure.machine k) q
  have outer:=sequential FixedPairParser.machine
    (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
    (CertificateGuardClosure.guard.seqRight (TotalIngressClosure.machine k) q)
  change (FixedPairParser.machine.seqRight
    (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
    (CertificateGuardClosure.guard.seqRight (TotalIngressClosure.machine k) q)).val=77+q.val
  rw [outer,inner]
  change 10+(67+q.val)=77+q.val
  omega
#print axioms sequential
#print axioms virtual_old
#print axioms carry_old
#print axioms body_old
#print axioms total_old
#print axioms guarded_old
end VirtualFinalClosure.StateFields
