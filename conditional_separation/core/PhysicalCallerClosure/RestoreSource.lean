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
private structure ReturnRows (entry out : Fin M.stateCount) where
  eSL : Fin M.stateCount
  eLH : Fin M.stateCount
  se : Safe entry
  scan : ∀ b,M.step entry (some b)=(entry,some b,.right)
  stop : M.step entry none=(eSL,none,.stay)
  reg : CrossRows (Safe:=Safe) .right eSL eLH
  beta : CrossRows (Safe:=Safe) .right eLH out
private theorem return_home {P lo S L H T entry out} (ls:lo ≤ S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,lo ≤ i → i < S → ∃ b,T i=some b)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b)
    (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (code:ReturnRows (Safe:=Safe) entry out) :
    Path M Safe P (H-lo+3) (node entry lo T) (node out H T) := by
  have scan:=sweepR entry T lo (S-lo) (P:=P) (by omega) code.se (by
    intro i a b
    obtain ⟨v,hv⟩:=source i a (by omega)
    rw [hv];exact code.scan v)
  rw [show lo+(S-lo)=S by omega] at scan
  have stop:=keep entry code.eSL S S T .stay (P:=P) (by omega) (by omega) code.se (by rw [ts];exact code.stop) rfl
  have r:=cross_right sl (show L ≤ P by omega) ts tl reg code.reg
  have b:=cross_right lh room tl th beta code.beta
  have whole:=scan.append (stop.append (r.append b))
  convert whole using 1
  omega
private structure RestoreOneRows (b : Bool) (entry out : Fin M.stateCount) where
  eL : Fin M.stateCount
  eS : Fin M.stateCount
  restore : Fin M.stateCount
  ret : Fin M.stateCount
  beta : CrossRows (Safe:=Safe) .left entry eL
  reg : CrossRows (Safe:=Safe) .left eL eS
  seek : CrossRows (Safe:=Safe) .left eS restore
  safeRestore : Safe restore
  write : M.step restore none=(ret,some b,.right)
  home : ReturnRows (Safe:=Safe) ret out
private theorem restore_one {P p S L H T b entry out}
    (physical:p < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (hole:T p=none) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,p < i → i < S → ∃ c,T i=some c)
    (reg:∀ i,S < i → i < L → ∃ c,T i=some c)
    (beta:∀ i,L < i → i < H → ∃ c,T i=some c)
    (code:RestoreOneRows (Safe:=Safe) b entry out) :
    Path M Safe P (2*(H-p)+6) (node entry H T) (node out H (put T p (some b))) := by
  have a:=cross_left lh room tl th beta code.beta
  have c:=cross_left sl (show L ≤ P by omega) ts tl reg code.reg
  have d:=cross_left physical (show S ≤ P by omega) hole ts source code.seek
  have w:=hop code.restore code.ret p (p+1) T (some b) .right (P:=P) (by omega) (by omega) code.safeRestore
    (by rw [hole];exact code.write) rfl
  let U:=put T p (some b)
  have low (i) (hi:p < i) : U i=T i:=by simp only [U,put,if_neg (show i≠p by omega)]
  have back:=return_home (T:=U) (lo:=p+1) (by omega) sl lh room
    (by rw [low S physical];exact ts) (by rw [low L (by omega)];exact tl) (by rw [low H (by omega)];exact th)
    (by intro i lo hi;rw [low i (by omega)];exact source i (by omega) hi)
    (by intro i lo hi;rw [low i (by omega)];exact reg i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact beta i lo hi) code.home
  have whole:=a.append (c.append (d.append (w.append back)))
  convert whole using 1
  omega
private structure RestoreTwoRows (a b : Bool) (entry out : Fin M.stateCount) where
  eL : Fin M.stateCount
  eS : Fin M.stateCount
  restoreA : Fin M.stateCount
  scan : Fin M.stateCount
  restoreB : Fin M.stateCount
  ret : Fin M.stateCount
  beta : CrossRows (Safe:=Safe) .left entry eL
  reg : CrossRows (Safe:=Safe) .left eL eS
  seek : CrossRows (Safe:=Safe) .left eS restoreA
  sa : Safe restoreA
  ss : Safe scan
  sb : Safe restoreB
  anchor : M.step restoreA none=(scan,some a,.left)
  occupied : ∀ b,M.step scan (some b)=(scan,some b,.left)
  hole : M.step scan none=(restoreB,none,.stay)
  table : M.step restoreB none=(ret,some b,.right)
  home : ReturnRows (Safe:=Safe) ret out
private theorem restore_two {P p anchor S L H T a b entry out}
    (order:p < anchor) (physical:anchor < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (tableHole:T p=none) (anchorHole:T anchor=none) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,p < i → i < S → i≠anchor → ∃ c,T i=some c)
    (reg:∀ i,S < i → i < L → ∃ c,T i=some c)
    (beta:∀ i,L < i → i < H → ∃ c,T i=some c)
    (code:RestoreTwoRows (Safe:=Safe) a b entry out) :
    Path M Safe P (2*(H-p)+7) (node entry H T)
      (node out H (put (put T anchor (some a)) p (some b))) := by
  have one:=cross_left lh room tl th beta code.beta
  have two:=cross_left sl (show L ≤ P by omega) ts tl reg code.reg
  have three:=cross_left physical (show S ≤ P by omega) anchorHole ts (by
    intro i lo hi;exact source i (by omega) hi (by omega)) code.seek
  have wa:=hop code.restoreA code.scan anchor (anchor-1) T (some a) .left (P:=P) (by omega) (by omega) code.sa
    (by rw [anchorHole];exact code.anchor) (by simp only [dest])
  let U:=put T anchor (some a)
  have same (i) (hi:i≠anchor) : U i=T i:=by simp only [U,put,if_neg hi]
  have scan:=sweepL code.scan U p (anchor-p-1) (P:=P) (by omega) code.ss (by
    intro i lo hi
    rw [same i (by omega)]
    obtain ⟨v,hv⟩:=source i lo (by omega) (by omega)
    rw [hv];exact code.occupied v)
  rw [show p+(anchor-p-1)=anchor-1 by omega] at scan
  have take:=keep code.scan code.restoreB p p U .stay (P:=P) (by omega) (by omega) code.ss
    (by rw [same p (by omega),tableHole];exact code.hole) rfl
  have wb:=hop code.restoreB code.ret p (p+1) U (some b) .right (P:=P) (by omega) (by omega) code.sb
    (by rw [same p (by omega),tableHole];exact code.table) rfl
  let V:=put U p (some b)
  have high (i) (hi:anchor < i) : V i=T i:=by simp only [V,U,put,if_neg (show i≠p by omega),if_neg (show i≠anchor by omega)]
  have occupied (i) (lo:p+1 ≤ i) (hi:i < S) : ∃ c,V i=some c:=by
    by_cases eq:i=anchor
    · subst i
      exact ⟨a,by simp only [V,U,put,if_neg (show anchor≠p by omega),if_true]⟩
    · obtain ⟨c,hc⟩:=source i (by omega) hi eq
      exact ⟨c,by simp only [V,U,put,if_neg (show i≠p by omega),if_neg eq,hc]⟩
  have back:=return_home (T:=V) (lo:=p+1) (by omega) sl lh room
    (by rw [high S physical];exact ts) (by rw [high L (by omega)];exact tl) (by rw [high H (by omega)];exact th)
    occupied (by intro i lo hi;rw [high i (by omega)];exact reg i lo hi)
    (by intro i lo hi;rw [high i (by omega)];exact beta i lo hi) code.home
  have whole:=one.append (two.append (three.append (wa.append (scan.append (take.append (wb.append back))))))
  convert whole using 1
  omega
end PhysicalCallerClosure
