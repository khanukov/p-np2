import CertificateGuardClosure.Raw
import CertificateGuardClosure.Audit
import CertificateGuardClosure.Fixtures
namespace VirtualFinalClosure
#check (CertificateGuardClosure.raw : ∀ k : Nat, CertificateGuardClosure.Target.Raw k)
#print axioms CertificateGuardClosure.raw
#print axioms CertificateGuardClosure.Audit.check_raw
end VirtualFinalClosure
