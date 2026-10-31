import Lean

/-- Parse literal imports using this pinned Lean, before ordering fresh sources. -/
def main (args : List String) : IO UInt32 := do
  let [request, output] := args | throw <| IO.userError "expected source requests and output"
  let input ← IO.FS.readFile request
  let requests ← IO.ofExcept <| (Lean.Json.parse input).bind Lean.Json.getArr?
  let mut result : Array Lean.Json := #[]
  for item in requests do
    let module ← IO.ofExcept <| item.getObjValAs? String "module"
    let source ← IO.ofExcept <| item.getObjValAs? String "source"
    let text ← IO.FS.readFile source
    let context := Lean.Parser.mkInputContext text source
    let (header, _, messages) ← Lean.Parser.parseHeader context
    let imports := Lean.Elab.headerToImports header
    if messages.hasErrors then throw <| IO.userError s!"source import parse failed: {source}"
    result := result.push <| Lean.Json.mkObj [
      ("module", Lean.toJson module), ("source", Lean.toJson source),
      ("isModule", Lean.toJson (Lean.Elab.HeaderSyntax.isModule header)),
      ("imports", Lean.toJson (imports.map fun (i : Lean.Import) => i.module.toString))]
  IO.FS.writeFile output (Lean.toJson result).compress
  return 0

#check (main : List String → IO UInt32)
#print axioms main
