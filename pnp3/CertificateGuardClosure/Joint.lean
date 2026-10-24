import TotalIngressClosure.Raw
import TotalIngressClosure.Audit
namespace CertificateGuardClosure
#check (TotalIngressClosure.raw : ∀ k : Nat, TotalIngressClosure.Target.Raw k)
#print axioms TotalIngressClosure.raw
#print axioms TotalIngressClosure.Audit.check_raw
end CertificateGuardClosure
