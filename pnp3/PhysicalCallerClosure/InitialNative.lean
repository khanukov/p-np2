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
private structure InitialRows (b : Bool) (entry : Fin M.stateCount) (gamma : Bool → Fin M.stateCount) where
  eL : Fin M.stateCount
  eS : Fin M.stateCount
  restore : Fin M.stateCount
  readAnchor : Fin M.stateCount
  beta : CrossRows (Safe:=Safe) .left entry eL
  reg : CrossRows (Safe:=Safe) .left eL eS
  seek : CrossRows (Safe:=Safe) .left eS restore
  sr : Safe restore
  sa : Safe readAnchor
  write : M.step restore none=(readAnchor,some b,.left)
  anchor : ∀ a,M.step readAnchor (some a)=(gamma a,none,.left)
private theorem initial_lift {P Mpos S L H T b a entry gamma}
    (positive:2 ≤ Mpos) (physical:Mpos < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (hole:T Mpos=none) (anchor:T (Mpos-1)=some a) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,Mpos < i → i < S → ∃ c,T i=some c)
    (reg:∀ i,S < i → i < L → ∃ c,T i=some c) (beta:∀ i,L < i → i < H → ∃ c,T i=some c)
    (code:InitialRows (Safe:=Safe) b entry gamma) :
    Path M Safe P (H-Mpos+5) (node entry H T)
      (node (gamma a) (Mpos-2) (put (put T Mpos (some b)) (Mpos-1) none)) := by
  have one:=cross_left lh room tl th beta code.beta
  have two:=cross_left sl (show L ≤ P by omega) ts tl reg code.reg
  have three:=cross_left physical (show S ≤ P by omega) hole ts source code.seek
  have restore:=hop code.restore code.readAnchor Mpos (Mpos-1) T (some b) .left (P:=P)
    (by omega) (by omega) code.sr (by rw [hole];exact code.write) (by simp only [dest])
  let U:=put T Mpos (some b)
  have ua:U (Mpos-1)=some a:=by simp only [U,put,if_neg (show Mpos-1≠Mpos by omega),anchor]
  have lift:=hop code.readAnchor (gamma a) (Mpos-1) (Mpos-2) U none .left (P:=P)
    (by omega) (by omega) code.sa (by rw [ua];exact code.anchor a) (by simp only [dest];omega)
  have whole:=one.append (two.append (three.append (restore.append lift)))
  convert whole using 1
  omega
private def GammaStopRows (entry out : Fin M.stateCount) : Prop:=
  ∃ marker:Fin M.stateCount,Safe entry ∧ Safe marker ∧
    M.step entry none=(marker,none,.right) ∧ M.step marker (some true)=(out,some true,.right)
private theorem gamma_stop {P low T entry out} (room:low+2 ≤ P) (hole:T low=none) (mark:T (low+1)=some true)
    (code:GammaStopRows (Safe:=Safe) entry out) :
    Path M Safe P 2 (node entry low T) (node out (low+2) T) := by
  obtain ⟨marker,se,sm,re,rm⟩:=code
  have one:=keep entry marker low (low+1) T .right (P:=P) (by omega) (by omega) se (by rw [hole];exact re) rfl
  have two:=keep marker out (low+1) (low+2) T .right (P:=P) (by omega) room sm (by rw [mark];exact rm) rfl
  exact one.append two
private theorem gamma_scan {P low hi T entry out} (order:low ≤ hi) (room:hi+2 ≤ P)
    (hole:T low=none) (mark:T (low+1)=some true)
    (source:∀ i,low < i → i ≤ hi → ∃ b,T i=some b) (safe:Safe entry)
    (loop:∀ b,M.step entry (some b)=(entry,some b,.left))
    (code:GammaStopRows (Safe:=Safe) entry out) :
    Path M Safe P (hi-low+2) (node entry hi T) (node out (low+2) T) := by
  have scan:=sweepL entry T low (hi-low) (P:=P) (by omega) safe (by
    intro i lo hi
    obtain ⟨b,hb⟩:=source i lo (by omega)
    rw [hb];exact loop b)
  rw [show low+(hi-low)=hi by omega] at scan
  exact scan.append (gamma_stop (by omega) hole mark code)
end PhysicalCallerClosure
