import FullIngressClosure.Execution
import FullIngressClosure.Raw
import Complexity.PrivateInterfaceLookupCoreFullIngress

/- Registered local adapters for the two monomorphic FullIngress interfaces.
   This is not a universal private-name scheme or a future-toolchain guarantee. -/
open Lean Elab Command Term Meta
namespace PartAPrivateControlRepair

def checkExact (n expectedOwner : Name) (expected : Syntax) : TermElabM Name :=
  PartAPrivateLookupCore.checkExact n expectedOwner 3 expected

def installChecked (rows : List (Name × Name × Name × Syntax × Name)) : CommandElabM Unit :=
  PartAPrivateLookupCore.installChecked (rows.map fun (o,u,a,t,n) => (o,u,a,3,t,n))

def installFullIngress : CommandElabM Unit := do
  let bodyType ← `(∀ k : Nat, BodyIngress.Target.Body k)
  let rawType ← `(∀ k : Nat, BodyIngress.Target.Body k → BodyIngress.Target.Raw k)
  installChecked [(`FullIngressClosure.Execution, `FullIngressClosure.body_complete,
      `FullIngressClosure.Execution, bodyType, `completeBody),
    (`FullIngressClosure.Raw, `FullIngressClosure.raw_of_body,
      `FullIngressClosure.Raw, rawType, `rawOfBody)]

#check (checkExact : Name → Name → Syntax → TermElabM Name)
#check (installChecked : List (Name × Name × Name × Syntax × Name) → CommandElabM Unit)
#check (installFullIngress : CommandElabM Unit)
#print axioms checkExact
#print axioms installChecked
#print axioms installFullIngress
end PartAPrivateControlRepair
