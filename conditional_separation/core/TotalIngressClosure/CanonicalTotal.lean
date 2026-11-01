import TotalIngressClosure.NegativeResult
import TotalIngressClosure.SupportedResult
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("CanonicalSpec","CanonicalResult","CanonicalResult"),
      ("FrontPartition","front_partition","frontPartition"),("NegativeResult","negative_result","negativeResult"),
      ("SupportedResult","supported_result","supportedResult")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") && n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique canonical all-input partition {mod}/{key}: {found.map Prod.fst}"
private theorem canonical_total (k:Nat){a m:Nat}(x:Bitstring a)(w:Bitstring m):CanonicalResult k x w:=by
  rcases frontPartition k x w with ⟨t,price,hit,heads,controls⟩|⟨n,z,tag,gamma,header,first,cap,rows⟩
  · exact negativeResult k x w t price hit heads controls
  · exact supportedResult k x w tag gamma header first cap rows
end TotalIngressClosure
