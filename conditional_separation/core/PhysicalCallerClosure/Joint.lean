import FullIngressClosure.Closure
import FullIngressClosure.Surface
import FullBodyClosure.Driver
import FullBodyClosure.BodySurface
namespace PhysicalCallerClosure
#check (FullIngressClosure.body : ∀ k : Nat, BodyIngress.Target.Body k)
#check (FullIngressClosure.raw : ∀ k : Nat, BodyIngress.Target.Raw k)
#check (FullBodyClosure.full_body : SerializedBody.Target.Body)
#print axioms FullIngressClosure.body
#print axioms FullIngressClosure.raw
#print axioms FullBodyClosure.full_body
#print axioms FullBodyClosure.full_body_mirror
end PhysicalCallerClosure
