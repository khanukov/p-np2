import PhysicalCallerClosure.AssignmentRows
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
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private structure PayRows (entry normal last : Fin M.stateCount) where
  scan : Fin M.stateCount
  back : Fin M.stateCount
  peek : Fin M.stateCount
  erase : Fin M.stateCount
  ret : Fin M.stateCount
  single : Fin M.stateCount
  home : Fin M.stateCount
  se : Safe entry
  ss : Safe scan
  sb : Safe back
  sp : Safe peek
  sx : Safe erase
  sr : Safe ret
  si : Safe single
  sh : Safe home
  enter : M.step entry none=(scan,none,.right)
  scanTrue : M.step scan (some true)=(scan,some true,.right)
  scanOther : ∀ b,b≠some true → M.step scan b=(back,b,.left)
  take : M.step back (some true)=(peek,some true,.left)
  multiple : M.step peek (some true)=(erase,some true,.right)
  one : M.step peek none=(single,none,.right)
  write : M.step erase (some true)=(ret,none,.left)
  retreat : M.step ret (some true)=(ret,some true,.left)
  stop : M.step ret none=(normal,none,.stay)
  keepLast : M.step single (some true)=(home,some true,.left)
  homeStop : M.step home none=(last,none,.stay)
private theorem payment_path (T : Nat → Option Bool) (H Q F P : Nat)
    (entry normal last : Fin M.stateCount) (code:PayRows (Safe:=Safe) entry normal last)
    (positive:0 < Q) (arena:H+Q < F) (room:F ≤ P) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none) :
    Path M Safe P (2*Q+5) (node entry H T)
      (node (if Q=1 then last else normal) H (if Q=1 then T else put T (H+Q) none)) := by
  have boundary:T (H+Q+1)≠some true:=by
    by_cases eq:H+Q+1=F
    · rw [eq,tf];decide
    · rw [gap _ (by omega) (by omega)];decide
  have e:=keep entry code.scan H (H+1) T .right (P:=P) (by omega) (by omega) code.se
    (by rw [th];exact code.enter) rfl
  have scan:=sweepR code.scan T (H+1) Q (P:=P) (by omega) code.ss (by
    intro i lo hi;rw [marks i (by omega) (by omega)];exact code.scanTrue)
  rw [show H+1+Q=H+Q+1 by omega] at scan
  have back:=keep code.scan code.back (H+Q+1) (H+Q) T .left (P:=P) (by omega) (by omega) code.ss
    (code.scanOther _ boundary) (by simp [dest])
  have peek:=keep code.back code.peek (H+Q) (H+(Q-1)) T .left (P:=P) (by omega) (by omega) code.sb
    (by rw [marks _ (by omega) le_rfl];exact code.take) (by simp only [dest];omega)
  by_cases one:Q=1
  · subst Q
    simp only [show H+(1-1)=H by omega] at peek
    have single:=keep code.peek code.single H (H+1) T .right (P:=P) (by omega) (by omega) code.sp
      (by rw [th];exact code.one) rfl
    have keepLast:=keep code.single code.home (H+1) H T .left (P:=P) (by omega) (by omega) code.si
      (by rw [marks _ (by omega) (by omega)];exact code.keepLast) (by simp [dest])
    have stop:=keep code.home last H H T .stay (P:=P) (by omega) (by omega) code.sh
      (by rw [th];exact code.homeStop) rfl
    simpa only [if_pos rfl] using e.append (scan.append (back.append (peek.append (single.append (keepLast.append stop)))))
  · have turn:=keep code.peek code.erase (H+(Q-1)) (H+Q) T .right (P:=P) (by omega) (by omega) code.sp
      (by rw [marks _ (by omega) (by omega)];exact code.multiple) (by simp only [dest];omega)
    have erase:=hop code.erase code.ret (H+Q) (H+(Q-1)) T none .left (P:=P) (by omega) (by omega) code.sx
      (by rw [marks _ (by omega) le_rfl];exact code.write) (by simp only [dest];omega)
    let U:=put T (H+Q) none
    have ret:=sweepL code.ret U H (Q-1) (P:=P) (by omega) code.sr (by
      intro i lo hi
      rw [show U i=T i by simp only [U,put,if_neg (show i≠H+Q by omega)],marks i lo (by omega)]
      exact code.retreat)
    have stop:=keep code.ret normal H H U .stay (P:=P) (by omega) (by omega) code.sr
      (by rw [show U H=T H by simp only [U,put,if_neg (show H≠H+Q by omega)],th];exact code.stop) rfl
    have whole:=e.append (scan.append (back.append (peek.append (turn.append (erase.append (ret.append stop))))))
    simp only [if_neg one]
    convert whole using 1
    omega
end PhysicalCallerClosure
