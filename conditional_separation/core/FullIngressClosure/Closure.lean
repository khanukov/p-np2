import FullIngressClosure.Execution
import FullIngressClosure.Raw
import Complexity.PrivateInterfaceLookupFullIngress
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd PartAPrivateControlRepair.installFullIngress
theorem body (k : Nat) : BodyIngress.Target.Body k := completeBody k
theorem raw (k : Nat) : BodyIngress.Target.Raw k := rawOfBody k (body k)
end FullIngressClosure
