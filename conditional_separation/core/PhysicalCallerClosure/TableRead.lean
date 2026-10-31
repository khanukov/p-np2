import PhysicalCallerClosure.AnchorReturn
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
run_cmd do
  let e←getEnv
  for leaf in ["AnchorReturnRows","anchor_return"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.AnchorReturn 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact table-return term {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.AnchorReturn do throwError "Wrong table-return owner"
    logInfo m!"table-read-support|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def boolTag (b : Bool) : Fin 3:=if b then ⟨1,by decide⟩ else ⟨0,by decide⟩
private structure TableReadRows (anchored : Bool) (entry : Fin M.stateCount) (out : Fin 3 → Fin M.stateCount) where
  ret : Bool → Fin M.stateCount
  eSL : Fin M.stateCount
  eLH : Fin M.stateCount
  se : Safe entry
  read : ∀ b,M.step entry (some b)=(ret b,none,.right)
  eof : M.step entry none=(eSL,none,.stay)
  physical : ∀ b,if anchored then Nonempty (AnchorReturnRows (Safe:=Safe) (ret b) (out (boolTag b)))
    else Nonempty (ReturnRows (Safe:=Safe) (ret b) (out (boolTag b)))
  reg : CrossRows (Safe:=Safe) .right eSL eLH
  beta : CrossRows (Safe:=Safe) .right eLH (out ⟨2,by decide⟩)
private theorem read_table {P p anchor S L H T anchored entry out}
    (ps:p ≤ S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,p < i → i < S → (anchored=false ∨ i≠anchor) → ∃ b,T i=some b)
    (cell:p < S → ∃ b,T p=some b)
    (anchorFrame:p < S → anchored=true → p < anchor ∧ anchor < S ∧ T anchor=none)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b) (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (code:TableReadRows (Safe:=Safe) anchored entry out) :
    ∃ tag:Fin 3,(tag.val=2 ↔ p=S) ∧ (tag.val=1 ↔ T p=some true) ∧
      Path M Safe P (H-p+3) (node entry p T) (node (out tag) H (put T p none)) := by
  by_cases phy:p < S
  · obtain ⟨b,hb⟩:=cell phy
    let U:=put T p none
    have high (i) (hi:p < i) : U i=T i:=by simp only [U,put,if_neg (show i≠p by omega)]
    have take:=hop entry (code.ret b) p (p+1) T none .right (P:=P) (by omega) (by omega) code.se
      (by rw [hb];exact code.read b) rfl
    have us:U S=none:=by rw [high S phy];exact ts
    have ul:U L=none:=by rw [high L (by omega)];exact tl
    have uh:U H=none:=by rw [high H (by omega)];exact th
    have ur:∀ i,S < i → i < L → ∃ b,U i=some b:=by intro i lo hi;rw [high i (by omega)];exact reg i lo hi
    have ub:∀ i,L < i → i < H → ∃ b,U i=some b:=by intro i lo hi;rw [high i (by omega)];exact beta i lo hi
    have retpath:Path M Safe P (H-(p+1)+3) (node (code.ret b) (p+1) U) (node (out (boolTag b)) H U):=by
      by_cases h:anchored=true
      · obtain ⟨pa,as,ah⟩:=anchorFrame phy h
        have codes:=code.physical b
        rw [if_pos h] at codes
        obtain ⟨home⟩:=codes
        exact anchor_return (T:=U) (by omega) as sl lh room (by rw [high anchor pa];exact ah) us ul uh (by
          intro i lo hi ne;rw [high i (by omega)];exact source i (by omega) hi (Or.inr ne)) ur ub home
      · have h0:anchored=false:=by cases anchored <;> simp_all
        have codes:=code.physical b
        rw [if_neg h] at codes
        obtain ⟨home⟩:=codes
        exact return_home (T:=U) (by omega) sl lh room us ul uh (by
          intro i lo hi;rw [high i (by omega)];exact source i (by omega) hi (Or.inl h0)) ur ub home
    refine ⟨boolTag b,?_,?_,?_⟩
    · have n2:(boolTag b).val≠2:=by cases b <;> decide
      constructor
      · intro bad;exact False.elim (n2 bad)
      · intro eq;omega
    · cases b <;> simp [boolTag,hb]
    · have whole:=take.append retpath
      convert whole using 1
      omega
  · have eq:p=S:=by omega
    subst p
    have one:=keep entry code.eSL S S T .stay (P:=P) (by omega) (by omega) code.se (by rw [ts];exact code.eof) rfl
    have r:=cross_right sl (show L ≤ P by omega) ts tl reg code.reg
    have b:=cross_right lh room tl th beta code.beta
    have whole:=one.append (r.append b)
    refine ⟨⟨2,by decide⟩,by simp,by simp [ts],?_⟩
    have unchanged:put T S none=T:=by funext i;by_cases hi:i=S <;> simp [put,hi,ts]
    rw [unchanged]
    convert whole using 1
    omega
end PhysicalCallerClosure
