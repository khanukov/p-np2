import FullWeight.Rows
namespace FullWeight
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for s in ["codes","before","power","middle","add","after","program","blen","powers","mlen","lookup_after","lookup_add","afterCodes","addCodes"] do
    let ns:=env.constants.toList.map Prod.fst |>.filter fun n => n.toString.startsWith "_private.FullWeight.Rows." && n.toString.endsWith (".FullWeight."++s)
    unless ns.length=1 do throwError "Ambiguous private row interface {s}: {ns}"
    logInfo m!"private-term|{ns.head!}"
    Lean.Elab.Command.modifyScope fun st => {st with openDecls := .explicit ((s.splitOn ".").foldl Name.str Name.anonymous) ns.head! :: st.openDecls}
private theorem lookup_middle (k i : Nat) (hi : i < 3) : (codes k)[795+246*k+i]?=(middle k)[i]? := by
  rw [program,List.append_assoc,List.append_assoc,List.append_assoc,List.getElem?_toArray,
    List.getElem?_append_right (by rw [blen];omega),blen,
    List.getElem?_append_right (by rw [powers];omega),powers]
  rw [show 795+246*k+i-795-246*k=i by omega,List.getElem?_append_left (by rw [mlen];omega)]
private theorem decode_row (k i code : Nat) (b : Option Bool)
    (lo : 64  ≤  i) (hi : i  ≤  798+93*k) (h65 : i  ≠  65) (h66 : i  ≠  66) (h67 : i  ≠  67)
    (got : (codes k)[3*(i-64)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  fromDonor "PowerDriver.Rows" "PowerDriver" "decode_row" => exact OLD k i code b lo hi h65 h66 h67 got
private def rowTac : TacticM Unit := withMainContext do
  let g ← getMainGoal;let target ← Lean.Meta.whnf (← instantiateMVars (← g.getType))
  let args:=target.getAppArgs[1]!.consumeMData.getAppArgs
  let src:=args[1]!.consumeMData.getAppArgs[1]!
  let rhs ← Lean.Meta.whnf target.getAppArgs[2]!
  let dst:=rhs.getAppArgs[2]!.consumeMData.getAppArgs[1]!
  let tail ← Lean.Meta.whnf rhs.getAppArgs[3]!
  let ov:=tail.getAppArgs[2]!;let mv ← Lean.Meta.whnf tail.getAppArgs[3]!
  let sym ← Lean.Meta.whnf ov
  let tag ← if sym.isAppOf ``Option.none then pure 0 else do
    let b ← Lean.Meta.whnf sym.getAppArgs.back!
    if b.isConstOf ``Bool.true then pure 2 else pure 1
  let move:=if mv.isConstOf ``Move.left then 0 else if mv.isConstOf ``Move.stay then 1 else 2
  let ke ← Term.elabTerm (mkIdent `k) none
  let je? := (← getLCtx).findFromUserName? `j |>.map fun d => d.toExpr
  let evalN (x : Expr) (k j : Nat) : TacticM Nat := do
    let x:=x.replaceFVar ke (mkNatLit k)
    let x:=match je? with | none => x | some e => x.replaceFVar e (mkNatLit j)
    let x ← Lean.Meta.withTransparency .all (Lean.Meta.whnf x)
    let some v:=x.rawNatLit? | throwError "Expected fixed affine row: {x}"
    pure v
  let s0 ← evalN src 0 0;let sk ← evalN src 1 0;let sj ← evalN src 0 1
  let d0 ← evalN dst 0 0;let dk ← evalN dst 1 0;let dj ← evalN dst 0 1
  let kv:=mkIdent `k;let jv:=mkIdent `j
  let sv ← if sj>s0 then `($(quote s0)+$(quote (sk-s0))*$kv:ident+$(quote (sj-s0))*$jv:ident) else `($(quote s0)+$(quote (sk-s0))*$kv:ident)
  let dv ← if dj>d0 then `($(quote d0)+$(quote (dk-d0))*$kv:ident+$(quote (dj-d0))*$jv:ident) else `($(quote d0)+$(quote (dk-d0))*$kv:ident)
  let cv ← `((9:Nat)*$dv:term+$(quote (3*tag+move)))
  let input ← Lean.Meta.whnf args[2]!
  let it ← if input.isAppOf ``Option.none then pure 0 else do
    let b ← Lean.Meta.whnf input.getAppArgs.back!
    if b.isConstOf ``Bool.true then pure 2 else pure 1
  let bv ← PrettyPrinter.delab args[2]!;let sr ← PrettyPrinter.delab src;let dr ← PrettyPrinter.delab dst
  let oo ← PrettyPrinter.delab ov;let mm ← PrettyPrinter.delab mv
  let offset:=quote (3*(s0-(if sk-s0=93 then 330 else if s0=329 then 329 else 330))+it)
  let literal ← if dj>d0 then `($(quote (9*d0+3*tag+move))+$(quote (9*(dk-d0)))*$kv:ident+$(quote (9*(dj-d0)))*$jv:ident) else `($(quote (9*d0+3*tag+move))+$(quote (9*(dk-d0)))*$kv:ident)
  let lookup ← if sk-s0=93 then `(tactic| rw [show 3*($sv:term-64)+$(quote it)=798+279*$kv:ident+$offset:term by omega,lookup_after $kv:ident $offset:term (by omega)])
    else if s0=329 then `(tactic| rw [show 3*($sv:term-64)+$(quote it)=795+246*$kv:ident+$offset:term by omega,lookup_middle $kv:ident $offset:term (by omega)])
    else `(tactic| rw [show 3*($sv:term-64)+$(quote it)=798+246*$kv:ident+33*$jv:ident+$offset:term by omega,lookup_add $kv:ident $jv:ident $offset:term (by omega) (by omega)])
  evalTactic (← `(tactic| (
    have se : $sr:term=$sv:term := by omega
    have de : $dr:term=$dv:term := by omega
    have a : $cv:term/9=$dv:term := by omega
    have b : $cv:term/3%3=$(quote tag) := by omega
    have c : $cv:term%3=$(quote move) := by omega
    have row := decode_row $kv:ident $sv:term $cv:term $bv:term (by omega) (by omega) (by omega) (by omega) (by omega) (by
      change (codes $kv:ident)[3*($sv:term-64)+$(quote it)]?=some $cv:term
      $lookup:tactic
      change some $literal:term=some $cv:term
      congr 1 <;> omega)
    have decoded : (Cursor.q $kv:ident ($cv:term/9),(if $cv:term/3%3=0 then none else some (decide ($cv:term/3%3=2))),(if $cv:term%3=0 then Move.left else if $cv:term%3=1 then Move.stay else Move.right))=(Cursor.q $kv:ident $dv:term,$oo:term,$mm:term) := by rw [a,b,c];rfl
    exact (congrArg (fun i : Nat => (Cursor.machine $kv:ident).step (Cursor.q $kv:ident i) $bv:term) se).trans (row.trans (decoded.trans (congrArg (fun i : Nat => (Cursor.q $kv:ident i,($oo:term : Option Bool),$mm:term)) de.symm))))))
private theorem row_check (k : Nat) : (Cursor.machine k).step (Cursor.q k (364+93*k)) none=(Cursor.q k (365+93*k),none,.right) := by run_tac rowTac
private def FourRows (k j : Nat) : Prop :=
  let s:=332+8*j+93*k
  (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right) ∧
  (Cursor.machine k).step (Cursor.q k (s+1)) (some true)=(Cursor.q k (s+1),some true,.right) ∧
  (Cursor.machine k).step (Cursor.q k (s+1)) (some false)=(Cursor.q k (s+2),some true,.left) ∧
  (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+3),none,.left) ∧
  (∀ b, (Cursor.machine k).step (Cursor.q k (s+2)) (some b)=(Cursor.q k (s+2),some b,.left)) ∧
  (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k (340+8*j+93*k),none,.stay) ∧
  (Cursor.machine k).step (Cursor.q k (s+3)) (some true)=(Cursor.q k (s+3),some true,.left) ∧
  (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k (336+8*j+93*k),none,.stay)
private theorem four0 (k : Nat) : FourRows k 0 := by
  dsimp only [FourRows]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | run_tac rowTac | intro bit;cases bit <;> run_tac rowTac
private theorem four1 (k : Nat) : FourRows k 1 := by
  dsimp only [FourRows]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | run_tac rowTac | intro bit;cases bit <;> run_tac rowTac
private theorem four2 (k : Nat) : FourRows k 2 := by
  dsimp only [FourRows]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | run_tac rowTac | intro bit;cases bit <;> run_tac rowTac
private theorem four3 (k : Nat) : FourRows k 3 := by
  dsimp only [FourRows]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | run_tac rowTac | intro bit;cases bit <;> run_tac rowTac
private theorem four_rows (k j : Nat) (hj : j < 4) : FourRows k j := by
  interval_cases j
  · exact four0 k
  · exact four1 k
  · exact four2 k
  · exact four3 k
end FullWeight
