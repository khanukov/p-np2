import RawFrontier.Audit
import RawFrontier.Fixtures
import RawFrontier.Pilot
open Lean in
run_cmd do
  let e ← getEnv
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
  for (n, ci) in e.constants.toList do
    let s := n.toString
    let isPublic := !n.isInternal && !(s.splitOn ".").any
      (fun c => "_".isPrefixOf c || "match_".isPrefixOf c)
    if s.startsWith "RawFrontier." && isPublic then logInfo m!"public-name|{n}"
    if s.startsWith "RawFrontier." && !isPublic then logInfo m!"internal-name|{n}"
    if let some i := e.getModuleIdxFor? n then
      if e.header.moduleNames[i]!.toString.startsWith "RawFrontier." then
        logInfo m!"owned-all-name|{n}"
        if isPublic then
          logInfo m!"owned-public-name|{n}"
          logInfo m!"owned-public-type|{n}|{ci.type}"
    else if isPublic then logInfo m!"owned-public-name|{n}"
    if (s.startsWith "_private.AllArityCursor.Runtime." &&
        ["er","exits","old_inert","raw_row","er_initial","map_er"].any
          (fun key => s.endsWith (".AllArityCursor."++key))) ||
        (s.startsWith "_private.Stream.Kernel." && s.endsWith ".Stream.install_exact") then
      logInfo m!"private-api|{n}|{ci.type}"
  logInfo m!"actual-option|maxHeartbeats|{(← getOptions).getNat `maxHeartbeats 200000}"
