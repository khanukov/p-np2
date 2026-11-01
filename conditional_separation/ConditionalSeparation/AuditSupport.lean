import Lean

namespace ConditionalSeparation.AuditSupport
open Lean Elab Term Command Meta

private def nameCode : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[Json.str "s", nameCode p, Json.str s]
  | .num p n => Json.arr #[Json.str "n", nameCode p, toJson n]
private def levelCode : Level → Json
  | .zero => Json.arr #[Json.str "z"]
  | .succ l => Json.arr #[Json.str "s", levelCode l]
  | .max a b => Json.arr #[Json.str "max", levelCode a, levelCode b]
  | .imax a b => Json.arr #[Json.str "imax", levelCode a, levelCode b]
  | .param n => Json.arr #[Json.str "p", nameCode n]
  | .mvar n => Json.arr #[Json.str "UNSUPPORTED_LEVEL_MVAR", nameCode n.name]
private def binderCode : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"
private def exprCode : Expr → Json
  | .bvar n => Json.arr #[Json.str "b", toJson n]
  | .sort l => Json.arr #[Json.str "s", levelCode l]
  | .const n ls => Json.arr #[Json.str "c", nameCode n, toJson (ls.map levelCode)]
  | .app f a => Json.arr #[Json.str "a", exprCode f, exprCode a]
  | .lam n t b bi => Json.arr #[Json.str "l", nameCode n, exprCode t, exprCode b, Json.str (binderCode bi)]
  | .forallE n t b bi => Json.arr #[Json.str "f", nameCode n, exprCode t, exprCode b, Json.str (binderCode bi)]
  | .letE n t v b nd => Json.arr #[Json.str "e", nameCode n, exprCode t, exprCode v, exprCode b, toJson nd]
  | .lit (.natVal n) => Json.arr #[Json.str "nat", toJson n]
  | .lit (.strVal s) => Json.arr #[Json.str "str", Json.str s]
  | .mdata _ e => exprCode e
  | .proj n i e => Json.arr #[Json.str "proj", nameCode n, toJson i, exprCode e]
  | .fvar n => Json.arr #[Json.str "UNSUPPORTED_FVAR", nameCode n.name]
  | .mvar n => Json.arr #[Json.str "UNSUPPORTED_MVAR", nameCode n.name]
private def kindCode : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def decodeName : Nat → Json → Except String Name
  | 0, _ => throw "name depth"
  | fuel + 1, j => do
    let a ← j.getArr?
    if a.isEmpty then return .anonymous
    unless a.size == 3 do throw "name arity"
    let parent ← decodeName fuel a[1]!
    match ← a[0]!.getStr? with
    | "s" => return .str parent (← a[2]!.getStr?)
    | "n" => return .num parent (← a[2]!.getNat?)
    | _ => throw "name tag"
private def decodeLevel : Nat → Json → Except String Level
  | 0, _ => throw "level depth"
  | fuel + 1, j => do
    let a ← j.getArr?
    if a.isEmpty then throw "empty level node"
    match ← a[0]!.getStr? with
    | "z" => if a.size == 1 then return .zero else throw "zero arity"
    | "s" => if a.size == 2 then return .succ (← decodeLevel fuel a[1]!) else throw "succ arity"
    | "p" => if a.size == 2 then return .param (← decodeName fuel a[1]!) else throw "param arity"
    | "max" => if a.size == 3 then return .max (← decodeLevel fuel a[1]!) (← decodeLevel fuel a[2]!) else throw "max arity"
    | "imax" => if a.size == 3 then return .imax (← decodeLevel fuel a[1]!) (← decodeLevel fuel a[2]!) else throw "imax arity"
    | _ => throw "unsupported level"
private def decodeBinder (j : Json) : Except String BinderInfo := do
  match ← j.getStr? with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => throw "binder tag"
private def decodeExpr : Nat → Json → Except String Expr
  | 0, _ => throw "type depth"
  | fuel + 1, j => do
    let a ← j.getArr?
    if a.isEmpty then throw "empty expression node"
    let arity (n : Nat) : Except String Unit := do
      unless a.size == n do throw "expression arity"
    match ← a[0]!.getStr? with
    | "b" => arity 2; return .bvar (← a[1]!.getNat?)
    | "s" => arity 2; return .sort (← decodeLevel fuel a[1]!)
    | "c" =>
      arity 3
      let levels ← (← a[2]!.getArr?).toList.mapM (decodeLevel fuel)
      return .const (← decodeName fuel a[1]!) levels
    | "a" => arity 3; return .app (← decodeExpr fuel a[1]!) (← decodeExpr fuel a[2]!)
    | "l" => arity 5; return .lam (← decodeName fuel a[1]!) (← decodeExpr fuel a[2]!) (← decodeExpr fuel a[3]!) (← decodeBinder a[4]!)
    | "f" => arity 5; return .forallE (← decodeName fuel a[1]!) (← decodeExpr fuel a[2]!) (← decodeExpr fuel a[3]!) (← decodeBinder a[4]!)
    | "e" => arity 6; return .letE (← decodeName fuel a[1]!) (← decodeExpr fuel a[2]!) (← decodeExpr fuel a[3]!) (← decodeExpr fuel a[4]!) (← a[5]!.getBool?)
    | "nat" => arity 2; return .lit (.natVal (← a[1]!.getNat?))
    | "str" => arity 2; return .lit (.strVal (← a[1]!.getStr?))
    | "proj" => arity 4; return .proj (← decodeName fuel a[1]!) (← a[2]!.getNat?) (← decodeExpr fuel a[3]!)
    | _ => throw "unsupported expression; free/metavariables forbidden"

/-- Alpha-renames only bound variable labels. BinderInfo, domains, order,
indices, constants, universe names and every premise/conclusion are preserved. -/
private def canonicalType : Expr → Expr
  | .lam _ t b bi => .lam .anonymous (canonicalType t) (canonicalType b) bi
  | .forallE _ t b bi => .forallE .anonymous (canonicalType t) (canonicalType b) bi
  | .letE _ t v b nd => .letE .anonymous (canonicalType t) (canonicalType v) (canonicalType b) nd
  | .app f a => .app (canonicalType f) (canonicalType a)
  | .mdata _ e => canonicalType e
  | .proj n i e => .proj n i (canonicalType e)
  | e => e
/-- Exact object schemas precede all literal use; unknown keys are rejected. -/
private def exactKeys (j : Json) (keys : List String) : Except String Unit := do
  let values ← keys.mapM j.getObjVal?
  unless j == Json.mkObj (keys.zip values) do throw "literal record schema"
private def validateBasic (j : Json) (keys : List String) : Except String (Name × Expr) := do
  exactKeys j keys
  let n ← decodeName 10000 (← j.getObjVal? "name_code")
  if n.isAnonymous then throw "anonymous contract identity"
  if (← (← j.getObjVal? "owner").getStr?).isEmpty then throw "empty contract owner"
  let kind ← (← j.getObjVal? "kind").getStr?
  unless ["definition", "theorem", "opaque", "inductive", "constructor", "recursor"].contains kind do
    throw "unsupported literal kind"
  let mut universes : Std.HashSet Name := {}
  for u in (← (← j.getObjVal? "universes").getArr?) do
    let name ← decodeName 10000 u
    if name.isAnonymous || universes.contains name then throw "literal universe identity"
    universes := universes.insert name
  let type ← decodeExpr 10000 (← j.getObjVal? "type")
  if type.hasLooseBVars then throw "loose literal type variable"
  return (n, type)
private def validateRecord (j : Json) : Except String Name := do
  let keys := ["name_code", "owner", "kind", "universes", "type"]
  let (n, type) ← validateBasic j (keys ++ ["private_guards"])
  let mut guards : Std.HashSet Name := {}
  for g in (← (← j.getObjVal? "private_guards").getArr?) do
    let (p, _) ← validateBasic g keys
    if !isPrivateName p || guards.contains p then throw "private guard identity/duplicate"
    guards := guards.insert p
  let refs := type.getUsedConstants.filter isPrivateName
  unless refs.size == guards.size && refs.all guards.contains do throw "private guard domain mismatch"
  return n
private def literalRef (values : Array Json) (j : Json) : Except String (Nat × Json) := do
  let i ← j.getNat?
  match values[i]? with
  | some value => return (i, value)
  | none => throw "forward/cyclic/out-of-bounds literal reference"
private def decodeDag (input : Json) : Except String (Array Json) := do
  let top ← input.getArr?
  unless top.size == 3 do throw "literal DAG outer arity"
  unless (← top[0]!.getStr?) == "literal-dag-v1" do throw "literal DAG version"
  let nodes ← top[1]!.getArr?
  let rootIds ← top[2]!.getArr?
  if nodes.isEmpty || rootIds.isEmpty then throw "empty literal DAG"
  let mut values : Array Json := #[]
  let mut edges : Array (Array Nat) := #[]
  let mut seen : Std.HashSet Json := {}
  for node in nodes do
    let a ← node.getArr?
    unless a.size == 2 do throw "literal node arity"
    let tag ← a[0]!.getStr?
    let mut deps : Array Nat := #[]
    let value ← match tag with
      | "str" => pure <| Json.str (← a[1]!.getStr?)
      | "nat" => pure <| toJson (← a[1]!.getNat?)
      | "bool" => pure <| toJson (← a[1]!.getBool?)
      | "array" => do
        let mut result := #[]
        for ref in (← a[1]!.getArr?) do
          let (id, value) ← literalRef values ref
          deps := deps.push id; result := result.push value
        pure <| Json.arr result
      | "object" => do
        let mut fields : List (String × Json) := []
        let mut previous : Option String := none
        for field in (← a[1]!.getArr?) do
          let pair ← field.getArr?
          unless pair.size == 2 do throw "literal object field arity"
          let key ← pair[0]!.getStr?
          if let some p := previous then
            unless p < key do throw "literal object key order/duplicate"
          previous := some key
          let (id, value) ← literalRef values pair[1]!
          deps := deps.push id; fields := (key, value) :: fields
        pure <| Json.mkObj fields.reverse
      | _ => throw "unknown literal node tag"
    if seen.contains node then throw "duplicate literal node"
    seen := seen.insert node
    values := values.push value; edges := edges.push deps
  let mut records : Array Json := #[]
  let mut names : Std.HashSet Name := {}
  let mut used : Array Bool := Array.replicate nodes.size false
  for ref in rootIds do
    let (id, row) ← literalRef values ref
    let n ← validateRecord row
    if names.contains n then throw "duplicate literal root identity"
    names := names.insert n
    records := records.push row
    used := used.set! id true
  for offset in [:nodes.size] do
    let id := nodes.size - 1 - offset
    if used[id]! then
      for dep in edges[id]! do
        used := used.set! dep true
  unless used.all id do throw "unused literal node"
  return records

/-- Reconstruct complete independent literal contracts from a validated shared DAG. -/
def decodeLiteralContracts (input : Json) : Except String (Array Json) :=
  decodeDag input

private def inlineContract (json : Json) : Except String Json := do
  let rows ← decodeLiteralContracts json
  unless rows.size == 1 do throw "inline literal contract count"
  return rows[0]!
private def isDag (json : Json) : Bool :=
  match json.getArr? with
  | .ok a => a[0]?.bind (fun x => x.getStr?.toOption) == some "literal-dag-v1"
  | .error _ => false

private def liftFrozen {α : Type} (x : Except String α) : TermElabM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "invalid frozen contract: {e}"
private def guardOne (row : Json) : TermElabM Expr := do
  let n ← liftFrozen (decodeName 10000 (← liftFrozen (row.getObjVal? "name_code")))
  let env ← getEnv
  let some ci := env.find? n | throwError "absent exact frozen constant {n}"
  unless ci.name == n do throwError "constant identity mismatch {n}"
  let owner ← match env.getModuleIdxFor? n with
    | some i => match env.header.moduleNames[i.toNat]? with
      | some module => pure module
      | none => throwError "module owner index out of bounds {n}"
    | none => pure env.header.mainModule
  let expectedOwner ← liftFrozen ((← liftFrozen (row.getObjVal? "owner")).getStr?)
  unless owner.toString == expectedOwner do throwError "actual owner mismatch {n}"
  let kind ← liftFrozen ((← liftFrozen (row.getObjVal? "kind")).getStr?)
  unless ["definition", "theorem", "opaque", "inductive", "constructor", "recursor"].contains kind do
    throwError "unsupported frozen declaration kind {kind}"
  unless kindCode ci == kind do throwError "declaration kind mismatch {n}"
  let ujson ← liftFrozen (row.getObjVal? "universes")
  unless toJson (ci.levelParams.map nameCode) == ujson do throwError "literal universe list mismatch {n}"
  let expected ← liftFrozen (row.getObjVal? "type")
  let type ← liftFrozen (decodeExpr 10000 expected)
  unless Expr.equal (canonicalType ci.type) (canonicalType type) do
    throwError "literal FULL type mismatch {n}"
  unless (← whnf (← inferType type)).isSort do throwError "frozen type is not a type"
  let literalUniverses ← liftFrozen ((← liftFrozen ujson.getArr?).toList.mapM (decodeName 10000))
  return .const n (literalUniverses.map Level.param)
private def guarded (row : Json) : TermElabM Expr := do
  for r in (← liftFrozen ((← liftFrozen (row.getObjVal? "private_guards")).getArr?)) do
    discard <| guardOne r
  guardOne row

private initialize literalTables : SimplePersistentEnvExtension
    (Name × Array Json) (Array (Name × Array Json)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.push entry
    addImportedFn := fun states => states.foldl (fun state entries => state ++ entries) #[] }

private def lookupLiteralRecords (env : Environment) (owner : Name) : Except String (Array Json) := do
  let entries := (literalTables.getState env).filter (fun entry => entry.1 == owner)
  unless entries.size == 1 do throw "absent or duplicate literal table owner"
  return entries[0]!.2

/-- Lookup only a uniquely registered exact module's independently frozen literal table. -/
def literalRecords (env : Environment) (owner : Name) : Except String (Array Json) :=
  lookupLiteralRecords env owner

private def isLiteralReference (json : Json) : Bool :=
  match json.getArr? with
  | .ok a => a[0]?.bind (fun x => x.getStr?.toOption) == some "literal-ref-v1"
  | .error _ => false
private def referenceContract (env : Environment) (json : Json) : Except String Json := do
  let a ← json.getArr?
  unless a.size == 4 do throw "literal reference arity"
  unless (← a[0]!.getStr?) == "literal-ref-v1" do throw "literal reference version"
  let label ← a[1]!.getStr?
  let owner := label.toName
  if owner.isAnonymous || owner.toString != label then throw "literal reference owner syntax"
  let rows ← literalRecords env owner
  let index ← a[2]!.getNat?
  let some row := rows[index]? | throw "literal record index out of bounds"
  let expectedName ← a[3]!.getStr?
  let actualName ← decodeName 10000 (← row.getObjVal? "name_code")
  unless actualName.toString == expectedName do throw "literal reference root identity"
  return row
private def resolveContract (env : Environment) (json : Json) : Except String Json :=
  if isDag json then inlineContract json
  else if isLiteralReference json then referenceContract env json
  else pure json

elab "literal_contracts% " values:str+ : command => do
  let text := String.join (values.toList.map (fun value => value.getString))
  let rows ← liftTermElabM do liftFrozen (decodeLiteralContracts (← liftFrozen (Json.parse text)))
  let env ← getEnv
  let owner := env.header.mainModule
  if (literalTables.getState env).any (fun entry => entry.1 == owner) then
    throwError "duplicate literal table registration {owner}"
  modifyEnv fun env => literalTables.addEntry env (owner, rows)

elab "frozen_type% " value:str : term => do
  let json ← liftFrozen (Json.parse value.getString)
  let json ← if isDag json || isLiteralReference json then do
    let row ← liftFrozen (resolveContract (← getEnv) json)
    liftFrozen (row.getObjVal? "type")
    else pure json
  let type ← liftFrozen (decodeExpr 10000 json)
  unless (← whnf (← inferType type)).isSort do throwError "frozen literal is not a type"
  return type

elab "checked_const% " value:str : term => do
  let row ← liftFrozen (Json.parse value.getString)
  let row ← liftFrozen (resolveContract (← getEnv) row)
  guarded row

elab "checked_root% " value:str : command => do
  let row ← liftTermElabM do liftFrozen (Json.parse value.getString)
  let row ← liftTermElabM do liftFrozen (resolveContract (← getEnv) row)
  let e ← liftTermElabM do guarded row
  let .const n _ := e | throwError "guarded root must be a constant"
  let env ← getEnv
  unless env.contains n do throwError "root absent before collectAxioms {n}"
  let axs ← collectAxioms n
  for a in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "nonallowed direct axiom {a} for {n}"
  let result := Json.mkObj [("name", toJson n.toString),
    ("axioms", toJson (axs.map (·.toString)))]
  logInfo m!"[FULL_DIRECT_ROOT] {result.compress}"

end ConditionalSeparation.AuditSupport
