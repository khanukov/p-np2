import PhysicalCallerClosure.SourcePrepare
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def support (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing Engine term {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong Engine kind: {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
  logInfo m!"copy-support|{actual}|{n}|{ci.type}"
  closeMainGoal `support (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["Node","Path","put","keep","hop","sweepL","sweepR","crossL","crossR","dest"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
    logInfo m!"copy-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac support "Node.mk" "constructor"
run_cmd do
  let e←getEnv
  for leaf in ["CrossRows","cross_left","cross_right"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.SourcePrepare 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing source navigation term {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.SourcePrepare do throwError "Wrong source navigation owner"
    logInfo m!"restore-source-support|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private structure TableSeekRows (entry out : Fin M.stateCount) where
  eL : Fin M.stateCount
  eS : Fin M.stateCount
  skipAnchor : Fin M.stateCount
  scan : Fin M.stateCount
  beta : CrossRows (Safe:=Safe) .left entry eL
  reg : CrossRows (Safe:=Safe) .left eL eS
  seek : CrossRows (Safe:=Safe) .left eS skipAnchor
  sa : Safe skipAnchor
  ss : Safe scan
  skip : M.step skipAnchor none=(scan,none,.left)
  occupied : ∀ b,M.step scan (some b)=(scan,some b,.left)
  hole : M.step scan none=(out,none,.stay)
private theorem seek_table {P p anchor S L H T entry out}
    (order:p < anchor) (physical:anchor < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (tableHole:T p=none) (anchorHole:T anchor=none) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,p < i → i < S → i≠anchor → ∃ c,T i=some c)
    (reg:∀ i,S < i → i < L → ∃ c,T i=some c)
    (beta:∀ i,L < i → i < H → ∃ c,T i=some c)
    (code:TableSeekRows (Safe:=Safe) entry out) :
    Path M Safe P (H-p+4) (node entry H T) (node out p T) := by
  have one:=cross_left lh room tl th beta code.beta
  have two:=cross_left sl (show L ≤ P by omega) ts tl reg code.reg
  have three:=cross_left physical (show S ≤ P by omega) anchorHole ts (by
    intro i lo hi;exact source i (by omega) hi (by omega)) code.seek
  have skip:=keep code.skipAnchor code.scan anchor (anchor-1) T .left (P:=P) (by omega) (by omega) code.sa
    (by rw [anchorHole];exact code.skip) (by simp only [dest])
  have scan:=sweepL code.scan T p (anchor-p-1) (P:=P) (by omega) code.ss (by
    intro i lo hi
    obtain ⟨v,hv⟩:=source i lo (by omega) (by omega)
    rw [hv];exact code.occupied v)
  rw [show p+(anchor-p-1)=anchor-1 by omega] at scan
  have take:=keep code.scan out p p T .stay (P:=P) (by omega) (by omega) code.ss
    (by rw [tableHole];exact code.hole) rfl
  have whole:=one.append (two.append (three.append (skip.append (scan.append take))))
  convert whole using 1
  omega
end PhysicalCallerClosure
