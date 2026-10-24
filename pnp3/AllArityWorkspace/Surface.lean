import AllArityWorkspace.Layout
import AllArityWorkspace.Audit
import AllArityWorkspace.Fixtures
import AllArityWorkspace.Nonvacuity
open Lean in
run_cmd do
  let e ← getEnv
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
  for (n, ci) in e.constants.toList do
    let s := n.toString
    let isPublic := !n.isInternal && !(s.splitOn ".").any
      (fun c => "_".isPrefixOf c || "match_".isPrefixOf c)
    if s.startsWith "AllArityWorkspace." && isPublic then logInfo m!"public-name|{n}"
    if s.startsWith "AllArityWorkspace." && !isPublic then logInfo m!"internal-name|{n}"
    if let some i := e.getModuleIdxFor? n then
      if e.header.moduleNames[i]!.toString.startsWith "AllArityWorkspace." then
        logInfo m!"owned-all-name|{n}"
        if isPublic then
          logInfo m!"owned-public-name|{n}"
          logInfo m!"owned-public-type|{n}|{ci.type}"
    else if isPublic then logInfo m!"owned-public-name|{n}"
    if (s.startsWith "_private.AllArityCounted.Runtime." &&
        (s.endsWith ".AllArityCounted.actual_cells" || s.contains '.')) ||
        (s.startsWith "_private.CappedWorkspace.Raw." && s.endsWith ".CappedWorkspace.suffix_bound") then
      if s.endsWith ".AllArityCounted.actual_cells" || s.endsWith ".CappedWorkspace.suffix_bound" ||
          (s.splitOn ".").contains "Cells" then
        logInfo m!"private-api|{n}|{ci.type}"
  logInfo m!"actual-option|maxHeartbeats|{(← getOptions).getNat `maxHeartbeats 200000}"
