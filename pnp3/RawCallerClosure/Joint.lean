import CertificateGuardClosure.Raw
import CertificateGuardClosure.Audit
import PhysicalCallerClosure.DriverSurface
import PhysicalCallerClosure.Entry
namespace RawCallerClosure
#check (CertificateGuardClosure.raw : ∀ k : Nat, CertificateGuardClosure.Target.Raw k)
#check (PhysicalCallerClosure.caller_rows : ∀ k : Nat, PhysicalCallerClosure.CallerRows k)
#print axioms CertificateGuardClosure.raw
#print axioms CertificateGuardClosure.Audit.check_raw
#print axioms PhysicalCallerClosure.caller_rows
#print axioms PhysicalCallerClosure.caller_rows_mirror
end RawCallerClosure
