import Complexity.PrivateInterfaceLookupResolvedSourceScan
import FullIngressClosure.SourceSkipDriver
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateSourceScan.bindings `FullIngressClosure.SourceSkipCertificates
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated source-scan identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private def entry9 (k : Nat) (bit : Bool) : Fin (BodyIngress.machine k).stateCount :=
  if bit then st k 1587 else st k 1547
private def entry11 (k : Nat) (bit : Bool) : Fin (BodyIngress.machine k).stateCount :=
  if bit then st k 1737 else st k 1675
private def finishEntry (k : Nat) (bit : Bool) : Fin (BodyIngress.machine k).stateCount :=
  if bit then st k 1919 else st k 1861
private def skip9Codes (k : Nat) : SkipCodes k 9 11 (entry9 k) (entry11 k) (st k 1855) (st k 1977) := by
  refine skipCodesMk (fun bit=>if bit then st k 1623 else st k 1583) ?_ ?_
  · intro bit
    cases bit
    · exact forward9_0 k
    · exact forward9_1 k
  · intro bit
    cases bit
    · exact zero9_0 k
    · exact zero9_1 k
private def skip11Codes (k : Nat) : SkipCodes k 11 0 (entry11 k) (finishEntry k) (st k 1855) (st k 1977) := by
  refine skipCodesMk (fun bit=>if bit then st k 1777 else st k 1715) ?_ ?_
  · intro bit
    cases bit
    · exact forward11_0 k
    · exact forward11_1 k
  · intro bit
    cases bit
    · exact zero11_0 k
    · exact zero11_1 k
end FullIngressClosure
