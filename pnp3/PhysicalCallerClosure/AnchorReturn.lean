import PhysicalCallerClosure.RestoreSource
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
run_cmd do
  let e←getEnv
  for leaf in ["ReturnRows","return_home"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.RestoreSource 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact source return term {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.RestoreSource do throwError "Wrong source return owner"
    logInfo m!"anchor-return-support|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private structure AnchorReturnRows (entry out : Fin M.stateCount) where
  afterAnchor : Fin M.stateCount
  se : Safe entry
  scan : ∀ b,M.step entry (some b)=(entry,some b,.right)
  skip : M.step entry none=(afterAnchor,none,.right)
  home : ReturnRows (Safe:=Safe) afterAnchor out
private theorem anchor_return {P lo anchor S L H T entry out}
    (order:lo ≤ anchor) (physical:anchor < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (hole:T anchor=none) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,lo ≤ i → i < S → i≠anchor → ∃ b,T i=some b)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b)
    (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (code:AnchorReturnRows (Safe:=Safe) entry out) :
    Path M Safe P (H-lo+3) (node entry lo T) (node out H T) := by
  have scan:=sweepR entry T lo (anchor-lo) (P:=P) (by omega) code.se (by
    intro i a b
    obtain ⟨v,hv⟩:=source i a (by omega) (by omega)
    rw [hv];exact code.scan v)
  rw [show lo+(anchor-lo)=anchor by omega] at scan
  have skip:=keep entry code.afterAnchor anchor (anchor+1) T .right (P:=P) (by omega) (by omega) code.se
    (by rw [hole];exact code.skip) rfl
  have back:=return_home (T:=T) (lo:=anchor+1) (by omega) sl lh room ts tl th (by
    intro i lo hi;exact source i (by omega) hi (by omega)) reg beta code.home
  have whole:=scan.append (skip.append back)
  convert whole using 1
  omega
end PhysicalCallerClosure
