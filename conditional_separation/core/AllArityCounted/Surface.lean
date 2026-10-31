import AllArityCounted.Audit
import AllArityCounted.Fixtures
import AllArityCounted.Nonvacuity
open Lean in
run_cmd do
  let e ← getEnv
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
  for (n, _) in e.constants.toList do
    let s := n.toString
    let isPublic := !n.isInternal && !(s.splitOn ".").any
      (fun c => "_".isPrefixOf c || "match_".isPrefixOf c)
    if s.startsWith "AllArityCounted." && isPublic then logInfo m!"public-name|{n}"
    if s.startsWith "AllArityCounted." && !isPublic then logInfo m!"internal-name|{n}"
    if let some i := e.getModuleIdxFor? n then
      if e.header.moduleNames[i]!.toString.startsWith "AllArityCounted." then
        logInfo m!"owned-all-name|{n}"
        if isPublic then logInfo m!"owned-public-name|{n}"
    else if isPublic then logInfo m!"owned-public-name|{n}"
