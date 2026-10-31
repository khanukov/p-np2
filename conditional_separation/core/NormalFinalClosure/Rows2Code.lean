import NormalFinalClosure.Machine2
import NormalFinalClosure.WordCache2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic Command Meta
private def exactV2 (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.NormalFinalClosure.Machine2 0) "NormalFinalClosure") leaf
  let some (.defnInfo ci):=e.find? n | throwError "Missing fixed v2 definition {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing v2 owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `NormalFinalClosure.Machine2 do throwError "Wrong v2 owner"
  logInfo m!"v2-row-definition|{n}|{ci.type}"
  closeMainGoal `exactV2 (mkConst n (ci.levelParams.map Level.param))
private abbrev instruction2 : Nat → Nat := by run_tac exactV2 "instruction2"
private abbrev actualRows2 : (k : Nat) → Fin (machine k).stateCount → Option Bool →
    Fin (machine k).stateCount × Option Bool × Move := by run_tac exactV2 "rows2"
run_cmd do
  let n:=Name.str (Name.str (Name.num `_private.NormalFinalClosure.Machine2 0) "NormalFinalClosure") "rows2"
  modifyScope fun s=>{s with openDecls:=.explicit `unfoldRows2 n::s.openDecls}
private theorem count2 (k : Nat) : (machine2 k).stateCount=(RawCallerClosure.machine k).stateCount+4715 := rfl
private def pc2 (k : Nat) (q : Fin 4715) : Fin (machine2 k).stateCount :=
  ⟨(RawCallerClosure.machine k).stateCount+q.val,by rw [count2];omega⟩
private def ns2 (k i : Nat) : Fin (machine2 k).stateCount :=
  pc2 k ⟨i%4715,Nat.mod_lt _ (by decide)⟩
private def symbol : Option Bool → Nat
  | none=>0 | some false=>1 | some true=>2
private def interpreted2 (k c : Nat) : Fin (machine2 k).stateCount × Option Bool × Move :=
  let target:=c/9
  let q:=if h:target<4715 then pc2 k ⟨target,h⟩
    else if target=4715 then (machine2 k).accept else (machine2 k).reject
  (q,(if c/3%3=0 then none else some (decide (c/3%3=2))),
    if c%3=0 then .left else if c%3=1 then .stay else .right)
private def Safe2 (k : Nat) (q : Fin (machine2 k).stateCount) : Prop :=
  (RawCallerClosure.machine k).stateCount≤q.val
private theorem ns2_safe (k i : Nat) : Safe2 k (ns2 k i) := by
  change (RawCallerClosure.machine k).stateCount≤(RawCallerClosure.machine k).stateCount+i%4715
  omega
private theorem native_code2 (k : Nat) (q : Fin 4715) (b : Option Bool) (c : Nat)
    (word:instruction2 (3*q.val+symbol b)=c) :
    (machine2 k).step (pc2 k q) b=interpreted2 k c := by
  have na:pc2 k q≠(machine2 k).accept := by
    intro bad
    have values:=congrArg (fun s : Fin (machine2 k).stateCount=>s.val) bad
    change (RawCallerClosure.machine k).stateCount+q.val=(RawCallerClosure.machine k).accept.val at values
    have bound:=(RawCallerClosure.machine k).accept.isLt
    omega
  have nr:pc2 k q≠(machine2 k).reject := by
    intro bad
    have values:=congrArg (fun s : Fin (machine2 k).stateCount=>s.val) bad
    change (RawCallerClosure.machine k).stateCount+q.val=(RawCallerClosure.machine k).reject.val at values
    have bound:=(RawCallerClosure.machine k).reject.isLt
    omega
  rw [UniformTM.step_of_ne (machine2 k) na nr]
  change unfoldRows2 k (pc2 k q) b=_
  dsimp only [unfoldRows2,pc2]
  rw [if_neg (by omega : ¬(RawCallerClosure.machine k).stateCount+q.val<(RawCallerClosure.machine k).stateCount)]
  simp only [Nat.add_sub_cancel_left]
  change interpreted2 k (instruction2 (3*q.val+symbol b))=interpreted2 k c
  exact congrArg (interpreted2 k) word
private def numeral? : Expr → Option Nat
  | .lit (.natVal n)=>some n | _=>none
private def romWord2 (i : Nat) : TacticM Nat := do
  let owner:=`NormalFinalClosure.Machine2
  let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure") ("block2_"++toString (i/256))
  let e←getEnv
  let some (.defnInfo ci):=e.find? n | throwError "Missing exact ROM block"
  let some mod:=e.getModuleIdxFor? n | throwError "Missing ROM block owner"
  unless mod.toNat<e.header.moduleNames.size && e.header.moduleNames[mod]! == owner do throwError "Wrong ROM block owner"
  let body:=ci.value.consumeMData
  unless body.isAppOfArity ``List.toArray 2 do throwError "Expected literal List.toArray/2"
  let args:=body.getAppArgs
  unless args.size==2 do throwError "Wrong ROM list constructor arity"
  let mut xs:=args[1]!
  for offset in [:i%256+1] do
    let cons←whnf xs
    unless cons.isAppOfArity ``List.cons 3 do throwError "ROM block index outside literal List.cons/3"
    let ca:=cons.getAppArgs
    unless ca.size==3 do throwError "Wrong ROM list-cell arity"
    if offset==i%256 then
      let some c:=numeral? (←whnf ca[1]!) | throwError "ROM cell is not a literal Nat"
      return c
    xs:=ca[2]!
  throwError "Unreachable bounded ROM lookup"
private def peelRomWord2 (offset : Nat) : TacticM Unit := do
  for _ in [:offset] do
    evalTactic (← `(tactic| rw [List.getElem!_cons_succ]))
  evalTactic (← `(tactic| rw [List.getElem!_cons_zero]))
private def nativeRow2 : TacticM Unit := withMainContext do
  let goal←getMainTarget
  unless goal.isAppOfArity ``Eq 3 do throwError "Expected Eq/3"
  let ea:=goal.getAppArgs
  unless ea.size==3 do throwError "Invalid Eq argument count"
  let lhs:=ea[1]!
  unless lhs.isAppOfArity ``UniformTM.step 3 do throwError "Expected actual UniformTM.step/3"
  let sa:=lhs.getAppArgs
  unless sa.size==3 do throwError "Invalid step argument count"
  unless sa[1]!.isAppOfArity ``ns2 2 do throwError "Expected fixed native PC constructor/2"
  let pa:=sa[1]!.getAppArgs
  unless pa.size==2 do throwError "Invalid native constructor argument count"
  let some i:=numeral? (←whnf pa[1]!) | throwError "PC must be a literal"
  unless i<4715 do throwError "PC outside finite ROM"
  let .fvar kid:=pa[0]! | throwError "Expected universally fixed k"
  let b:=sa[2]!
  let sym←if b.isAppOfArity ``Option.none 1 then pure 0 else do
    unless b.isAppOfArity ``Option.some 2 do throwError "Expected literal Option Bool"
    let ba:=b.getAppArgs
    unless ba.size==2 do throwError "Invalid some argument count"
    if ba[1]!.isConstOf ``Bool.false then pure 1 else if ba[1]!.isConstOf ``Bool.true then pure 2 else throwError "Expected literal Bool"
  let c←romWord2 (3*i+sym)
  let ks:TSyntax `term:=⟨mkIdent (←kid.getDecl).userName⟩
  let is:TSyntax `term:=⟨Syntax.mkNumLit (toString i)⟩
  let cs:TSyntax `term:=⟨Syntax.mkNumLit (toString c)⟩
  let bs←PrettyPrinter.delab b
  let os:TSyntax `term:=⟨Syntax.mkNumLit (toString ((3*i+sym)%256))⟩
  let owner:=`NormalFinalClosure.Machine2
  let stem:=Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure"
  let instr:TSyntax `ident:=⟨mkIdent (Name.str stem "instruction2")⟩
  let block:TSyntax `ident:=⟨mkIdent (Name.str stem ("block2_"++toString ((3*i+sym)/256)))⟩
  let blockNo:=(3*i+sym)/256
  let offset:=(3*i+sym)%256
  if blockNo<56 then
    let cacheOwner:=`NormalFinalClosure.WordCache2
    let cacheStem:=Name.str (Name.num (Name.append `_private cacheOwner) 0) "NormalFinalClosure"
    let blockName:=Name.str cacheStem ("blockEq_"++toString blockNo)
    let dropName:=Name.str cacheStem ("dropEq_"++toString blockNo++"_"++toString (offset/64))
    let wordsName:=Name.str cacheStem ("words_"++toString blockNo++"_0")
    let nthName:=Name.str cacheStem "nth_drop"
    let e←getEnv
    for (n,kind) in [(blockName,true),(dropName,true),(wordsName,false),(nthName,true)] do
      let some ci:=e.find? n | throwError "Missing exact ROM cache {n}"
      let actual:=match ci with|.thmInfo _=>some true|.defnInfo _=>some false|_=>none
      unless actual==some kind do throwError "Wrong ROM cache kind"
      let some md:=e.getModuleIdxFor? n | throwError "Missing cache owner"
      unless md.toNat<e.header.moduleNames.size && e.header.moduleNames[md]! == cacheOwner do throwError "Wrong cache owner"
    let be:TSyntax `term:=⟨mkIdent blockName⟩
    let de:TSyntax `term:=⟨mkIdent dropName⟩
    let ws:TSyntax `term:=⟨mkIdent wordsName⟩
    let nth:TSyntax `term:=⟨mkIdent nthName⟩
    let dr:TSyntax `term:=⟨Syntax.mkNumLit (toString (64*(offset/64)))⟩
    let rm:TSyntax `term:=⟨Syntax.mkNumLit (toString (offset%64))⟩
    let bn:TSyntax `term:=⟨Syntax.mkNumLit (toString blockNo)⟩
    let sy:TSyntax `term:=⟨Syntax.mkNumLit (toString sym)⟩
    let bt:TSyntax `term:=⟨block.raw⟩
    evalTactic (← `(tactic| refine (native_code2 $ks ⟨$is,by decide⟩ $bs $cs (by
      dsimp only [symbol]
      unfold instruction2
      unfold $instr
      have divId : (3 * $is + $sy) / 256 = $bn := by decide
      have modId : (3 * $is + $sy) % 256 = $os := by decide
      rewrite [divId,modId]
      change ($bt)[$os]! = $cs
      rewrite [($be),List.getElem!_toArray]
      have part:=($nth) $ws $dr $rm
      have addId : $dr + $rm = $os := by decide
      rewrite [addId] at part
      rewrite [←part,($de)]
      rfl)).trans ?_))
  else
    evalTactic (← `(tactic| refine (native_code2 $ks ⟨$is,by decide⟩ $bs $cs (by
      dsimp only [symbol]
      unfold instruction2
      unfold $instr
      unfold $block
      rw [List.getElem!_toArray]
      run_tac peelRomWord2 $os)).trans ?_))
  evalTactic (← `(tactic| apply Prod.ext))
  evalTactic (← `(tactic| apply Fin.ext))
  evalTactic (← `(tactic| rfl))
  evalTactic (← `(tactic| rfl))
end NormalFinalClosure
