import PowerDriver.Rows
namespace PowerDriver
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
private def rowNames : Name × Name := by
  run_tac do
    let names := (← getEnv).constants.toList.map Prod.fst
    let select (key : String) : TacticM Name := do
      let found:=names.filter fun n => n.toString.startsWith "_private.PowerDriver.Rows." && n.toString.endsWith (".PowerDriver."++key)
      unless found.length=1 do throwError "Ambiguous indexed row term: {found}"
      logInfo m!"private-term|{found.head!}"
      return found.head!
    let phase ← select "phase_row"; let codes ← select "instructions"
    evalTactic (← `(tactic| exact ($(quote phase),$(quote codes))))
private def rowTac : TacticM Unit := withMainContext do
  let goal ← getMainGoal; let target ← Lean.Meta.whnf (← instantiateMVars (← goal.getType))
  unless target.isAppOfArity ``Eq 3 do throwError "power row equality expected"
  let args := target.getAppArgs[1]!.consumeMData.getAppArgs
  unless args.size=3 do throwError "literal expected UniformTM.step"
  let stateArgs := args[1]!.consumeMData.getAppArgs
  unless stateArgs.size=2 do throwError "literal expected Cursor.q"
  let rhs ← Lean.Meta.whnf target.getAppArgs[2]!; let qa := rhs.getAppArgs
  unless qa.size=4 do throwError "literal expected pair"
  let da := qa[2]!.consumeMData.getAppArgs
  unless da.size=2 do throwError "literal expected destination Cursor.q"
  let tail ← Lean.Meta.whnf qa[3]!; let ta := tail.getAppArgs
  unless ta.size=4 do throwError "literal expected symbol/move pair"
  let sym ← Lean.Meta.whnf ta[2]!; let tag ← if sym.isAppOf ``Option.none then pure 0 else do
    let ba ← Lean.Meta.whnf sym.getAppArgs.back!
    if ba.isConstOf ``Bool.true then pure 2 else if ba.isConstOf ``Bool.false then pure 1 else throwError "literal expected fixed symbol: {sym}"
  let mv ← Lean.Meta.whnf ta[3]!
  let move ← if mv.isConstOf ``Move.left then pure 0 else if mv.isConstOf ``Move.stay then pure 1 else if mv.isConstOf ``Move.right then pure 2 else throwError "literal expected fixed move"
  let jv:=mkIdent `j; let ke ← Term.elabTerm (mkIdent `k) none; let je ← Term.elabTerm jv none
  let src0 ← Lean.Meta.withTransparency .all (Lean.Meta.whnf (stateArgs[1]!.replaceFVar je (mkNatLit 0)))
  let dst0 ← Lean.Meta.withTransparency .all (Lean.Meta.whnf ((da[1]!.replaceFVar je (mkNatLit 0)).replaceFVar ke (mkNatLit 0)))
  let some sourceBase:=src0.rawNatLit? | throwError "Expected fixed indexed source: {src0}"
  let some targetBase:=dst0.rawNatLit? | throwError "Expected fixed indexed destination: {dst0}"
  let sv ← `($(quote sourceBase)+82*$jv:ident)
  let kv ← PrettyPrinter.delab stateArgs[0]!
  let dv ← if targetBase==798 then `((798:Nat)+93*$kv:term) else `($(quote targetBase)+82*$jv:ident)
  let cv ← `((9:Nat)*$dv:term+$(quote (3*tag+move)))
  let sourceRaw ← PrettyPrinter.delab stateArgs[1]!; let targetRaw ← PrettyPrinter.delab da[1]!
  let input ← Lean.Meta.whnf args[2]!
  let inputTag ← if input.isAppOf ``Option.none then pure 0 else do
    let bit ← Lean.Meta.whnf input.getAppArgs.back!
    if bit.isConstOf ``Bool.true then pure 2 else if bit.isConstOf ``Bool.false then pure 1 else throwError "Fixed input tag expected"
  let bv ← PrettyPrinter.delab args[2]!; let tagv:=quote tag; let movev:=quote move; let iv:=quote inputTag; let ixv:=quote (3*(sourceBase-329)+inputTag)
  let phaseId:=mkIdent rowNames.1; let insId:=mkIdent rowNames.2
  let ov ← PrettyPrinter.delab ta[2]!; let mvv ← PrettyPrinter.delab ta[3]!
  let literal ← if targetBase==798 then `($(quote (9*targetBase+3*tag+move))+837*$kv:term) else `($(quote (9*targetBase+3*tag+move))+738*$jv:ident)
  evalTactic (← `(tactic| (
    have sourceEq : $sourceRaw:term=$sv:term := by omega
    have targetEq : $targetRaw:term=$dv:term := by omega
    have checkedRow := $phaseId:ident $kv:term $jv:ident $sv:term $cv:term $bv:term (by omega) (by omega) (by omega) (by
      have indexEq : 3*($sv:term-(329+82*$jv:ident))+$iv:term=$ixv:term := by omega
      change ($insId:ident $kv:term $jv:ident)[3*($sv:term-(329+82*$jv:ident))+$iv:term]?=some $cv:term
      rw [indexEq]
      change some $literal:term=some $cv:term
      congr 1 <;> omega)
    have destEq : $cv:term / 9=$dv:term := by omega
    have symbolEq : $cv:term / 3 % 3=$tagv:term := by omega
    have moveEq : $cv:term % 3=$movev:term := by omega
    have decoded : (Cursor.q $kv:term ($cv:term/9),(if $cv:term/3%3=0 then none else some (decide ($cv:term/3%3=2))),(if $cv:term%3=0 then Move.left else if $cv:term%3=1 then Move.stay else Move.right))=(Cursor.q $kv:term $dv:term,$ov:term,$mvv:term) := by
      rw [destEq,symbolEq,moveEq]; rfl
    have before:=congrArg (fun i : Nat => (Cursor.machine $kv:term).step (Cursor.q $kv:term i) $bv:term) sourceEq
    have after:=congrArg (fun i : Nat => (Cursor.q $kv:term i,($ov:term : Option Bool),$mvv:term)) targetEq.symm
    exact before.trans (checkedRow.trans (decoded.trans after)))))
private theorem checkEntry (k j : Nat) (hk : j<k) : (Cursor.machine k).step (Cursor.q k (329+82*j)) none=(Cursor.q k (330+82*j),none,.right) := by run_tac rowTac
private theorem checkChange (k j : Nat) (hk : j<k) : (Cursor.machine k).step (Cursor.q k (357+82*j)) (some false)=(Cursor.q k (358+82*j),some true,.left) := by run_tac rowTac
private theorem checkCap (k j : Nat) (hk : j<k) : (Cursor.machine k).step (Cursor.q k (410+82*j)) none=(Cursor.q k (798+93*k),none,.stay) := by run_tac rowTac
end PowerDriver
