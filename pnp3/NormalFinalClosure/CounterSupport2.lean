import NormalFinalClosure.Rows2Code
import NormalFinalClosure.Support
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic Meta
private def getSupport (owner ns : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
  let some ci:=e.find? n | throwError "Missing exact certificate support {n}"
  let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
  unless actual==kind do throwError "Wrong certificate support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing certificate owner"
  unless i.toNat < e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong certificate owner"
  logInfo m!"native-cert-support|{n}|{ci.type}"
  closeMainGoal `getSupport (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["RouteR","RouteL","ClearRows","DecRows","IncRows"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing exact row/route support {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing route owner"
      unless i.toNat < e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong route owner"
      logInfo m!"native-cert-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev nativeRow : TacticM Unit := by
  run_tac getSupport `NormalFinalClosure.Rows2Code `NormalFinalClosure "nativeRow2" "definition"
private abbrev instruction : Nat → Nat := by
  run_tac getSupport `NormalFinalClosure.Rows2Code `NormalFinalClosure "instruction2" "definition"
private theorem nsSafe : ∀ k i,Safe2 k (ns2 k i) := by
  run_tac getSupport `NormalFinalClosure.Rows2Code `NormalFinalClosure "ns2_safe" "theorem"
private def numeral? : Expr → Option Nat
  | .lit (.natVal n)=>some n | _=>none
private abbrev word : Nat → TacticM Nat := by
  run_tac getSupport `NormalFinalClosure.Rows2Code `NormalFinalClosure "romWord2" "definition"
private def nativeRoute : Nat → TacticM Unit
  | 0=>throwError "Route exceeds thirteen physical fields"
  | fuel+1=>withMainContext do
    let goal←getMainTarget
    let right:=goal.isAppOfArity ``RouteR 6
    unless right||goal.isAppOfArity ``RouteL 6 do throwError "Expected RouteR/6 or RouteL/6"
    let ga:=goal.getAppArgs
    unless ga.size==6 do throwError "Wrong route arity"
    let some i:=numeral? (←whnf ga[2]!) | throwError "Nonliteral origin field"
    let some j:=numeral? (←whnf ga[3]!) | throwError "Nonliteral destination field"
    if i==j then
      if right then evalTactic (← `(tactic|exact RouteR.nil _ _))
      else evalTactic (← `(tactic|exact RouteL.nil _ _))
    else
      unless (if right then i < j else j < i) do throwError "Bad route direction"
      unless ga[4]!.isAppOfArity ``ns2 2 do throwError "Expected fixed native constructor/2"
      let qa:=ga[4]!.getAppArgs
      unless qa.size==2 do throwError "Wrong native arity"
      let some e:=numeral? (←whnf qa[1]!) | throwError "Nonliteral native control"
      let .fvar kid:=qa[0]! | throwError "Expected universally fixed k"
      let ec←word (3*e)
      let scan:=ec/9
      unless ec%9==(if right then 2 else 0)&&scan < 4715 do throwError "Wrong literal route entry"
      let sc←word (3*scan)
      let next:=sc/9
      unless sc%9==1&&next < 4715 do throwError "Wrong literal route delimiter"
      let ks:TSyntax `term:=⟨mkIdent (←kid.getDecl).userName⟩
      let es:TSyntax `term:=⟨Syntax.mkNumLit (toString e)⟩
      let ss:TSyntax `term:=⟨Syntax.mkNumLit (toString scan)⟩
      let qs:TSyntax `term:=⟨Syntax.mkNumLit (toString next)⟩
      if right then
        evalTactic (← `(tactic|refine RouteR.next (s:=ns2 $ks $ss) (q:=ns2 $ks $qs) (nsSafe $ks $es) (nsSafe $ks $ss) ?_ ?_ ?_ ?_))
      else
        evalTactic (← `(tactic|refine RouteL.next (s:=ns2 $ks $ss) (q:=ns2 $ks $qs) (nsSafe $ks $es) (nsSafe $ks $ss) ?_ ?_ ?_ ?_))
      nativeRow
      evalTactic (← `(tactic|intro b;cases b))
      nativeRow
      nativeRow
      nativeRow
      nativeRoute fuel

end NormalFinalClosure
