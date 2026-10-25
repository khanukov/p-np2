import FullIngressClosure.Execution
import FullIngressClosure.Raw
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("Execution","body_complete","completeBody"),("Raw","raw_of_body","rawOfBody")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.FullIngressClosure."++mod++".") &&
      n.toString.endsWith (".FullIngressClosure."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique original full contract proof {mod}/{key}: {found.map Prod.fst}"
theorem body (k : Nat) : BodyIngress.Target.Body k := completeBody k
theorem raw (k : Nat) : BodyIngress.Target.Raw k := rawOfBody k (body k)
end FullIngressClosure
