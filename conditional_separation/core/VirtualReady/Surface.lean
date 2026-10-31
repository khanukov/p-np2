import VirtualReady.Audit
open Lean in
run_cmd do
  let e ← getEnv
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
  for (n, ci) in e.constants.toList do
    let s := n.toString
    let isPublic := !n.isInternal && !(s.splitOn ".").any
      (fun c => "_".isPrefixOf c || "match_".isPrefixOf c)
    if s.startsWith "VirtualReady." && isPublic then logInfo m!"public-name|{n}"
    if s.startsWith "VirtualReady." && !isPublic then logInfo m!"internal-name|{n}"
    if let some i := e.getModuleIdxFor? n then
      if e.header.moduleNames[i]!.toString.startsWith "VirtualReady." then
        logInfo m!"owned-all-name|{n}"
        if isPublic then
          logInfo m!"owned-public-name|{n}"
          logInfo m!"owned-public-module|{n}|{e.header.moduleNames[i]!}"
          logInfo m!"owned-public-type|{n}|{ci.type}"
        else logInfo m!"owned-private-type|{n}|{ci.type}"
open Lean in
run_cmd do
  logInfo m!"registered-option|maxHeartbeats|{Lean.maxHeartbeats.get (← getOptions)}"
  logInfo m!"registered-option|maxRecDepth|{Lean.maxRecDepth.get (← getOptions)}"
open Lean in
run_cmd do
  let e ← getEnv
  let keys := ["program","before","after","power","middle","add"] ++
    (List.range 12).map (fun j => "before" ++ toString j)
  for key in keys do
    let ns := e.constants.toList.filter fun (n, _) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith (".Cursor." ++ key)
    unless ns.length == 1 do throwError "Ambiguous pinned Cursor API {key}"
    for (n, ci) in ns do logInfo m!"cursor-private-selection|{key}|{n}|{ci.type}"
