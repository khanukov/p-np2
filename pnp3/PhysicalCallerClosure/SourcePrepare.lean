import PhysicalCallerClosure.Navigation
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
private def CrossRows (dir : Move) (entry out : Fin M.stateCount) : Prop :=
  ∃ scan : Fin M.stateCount,Safe entry ∧ Safe scan ∧
    M.step entry none=(scan,none,dir) ∧
    (∀ b,M.step scan (some b)=(scan,some b,dir)) ∧ M.step scan none=(out,none,.stay)
private theorem cross_left {P a b T entry out} (ab:a < b) (room:b ≤ P)
    (lo:T a=none) (hi:T b=none) (cells:∀ i,a < i → i < b → ∃ v,T i=some v)
    (code:CrossRows (Safe:=Safe) .left entry out) :
    Path M Safe P (b-a+1) (node entry b T) (node out a T) := by
  rcases code with ⟨scan,se,ss,re,rs,rn⟩
  have path:=crossL entry scan out T a (b-a-1) (P:=P) (by omega) se ss lo
    (by rwa [show a+(b-a-1)+1=b by omega]) (by
      intro i hl hu;exact cells i hl (by omega)) re rs rn
  simpa only [show a+(b-a-1)+1=b by omega,show b-a-1+2=b-a+1 by omega] using path
private theorem cross_right {P a b T entry out} (ab:a < b) (room:b ≤ P)
    (lo:T a=none) (hi:T b=none) (cells:∀ i,a < i → i < b → ∃ v,T i=some v)
    (code:CrossRows (Safe:=Safe) .right entry out) :
    Path M Safe P (b-a+1) (node entry a T) (node out b T) := by
  rcases code with ⟨scan,se,ss,re,rs,rn⟩
  have path:=crossR entry scan out T a (b-a-1) (P:=P) (by omega) se ss lo
    (by rwa [show a+(b-a-1)+1=b by omega]) (by
      intro i hl hu;exact cells i hl (by omega)) re rs rn
  simpa only [show a+(b-a-1)+1=b by omega,show b-a-1+2=b-a+1 by omega] using path
private def PrepareRows (b : Bool) (entry out : Fin M.stateCount) : Prop :=
  ∃ eL eS a read ret eSL eLH : Fin M.stateCount,
    CrossRows (Safe:=Safe) .left entry eL ∧ CrossRows (Safe:=Safe) .left eL eS ∧
    CrossRows (Safe:=Safe) .left eS a ∧ Safe a ∧ Safe read ∧ Safe ret ∧
    M.step a none=(read,none,.right) ∧ M.step read (some b)=(ret,none,.right) ∧
    (∀ c,M.step ret (some c)=(ret,some c,.right)) ∧ M.step ret none=(eSL,none,.stay) ∧
    CrossRows (Safe:=Safe) .right eSL eLH ∧ CrossRows (Safe:=Safe) .right eLH out
private theorem prepare_source_path {P S L H Mpos T b entry out}
    (positive:0 < Mpos) (physical:Mpos < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (ts:T S=none) (tl:T L=none) (th:T H=none) (anchor:T (Mpos-1)=none) (bit:T Mpos=some b)
    (source:∀ i,Mpos ≤ i → i < S → ∃ c,T i=some c)
    (reg:∀ i,S < i → i < L → ∃ c,T i=some c)
    (beta:∀ i,L < i → i < H → ∃ c,T i=some c)
    (code:PrepareRows (Safe:=Safe) b entry out) :
    Path M Safe P (2*(H-Mpos)+8) (node entry H T) (node out H (put T Mpos none)) := by
  rcases code with ⟨eL,eS,a,read,ret,eSL,eLH,cHL,cLS,cSA,sa,sread,sret,ra,rr,rs,rn,cSL,cLH⟩
  have one:=cross_left lh room tl th beta cHL
  have two:=cross_left (P:=P) sl (by omega) ts tl reg cLS
  have three:=cross_left (show Mpos-1 < S by omega) (show S ≤ P by omega) anchor ts
    (by intro i lo hi;exact source i (by omega) hi) cSA
  have a1:=keep a read (Mpos-1) Mpos T .right (P:=P) (by omega) (by omega) sa
    (by rw [anchor];exact ra) (by simp only [dest];omega)
  have a2:=hop read ret Mpos (Mpos+1) T none .right (P:=P) (by omega) (by omega) sread
    (by rw [bit];exact rr) rfl
  let U:=put T Mpos none
  have unchanged:∀ i,i≠Mpos → U i=T i:=by intro i hi;simp only [U,put,if_neg hi]
  have us:U S=none:=by rw [unchanged S (by omega),ts]
  have ul:U L=none:=by rw [unchanged L (by omega),tl]
  have uh:U H=none:=by rw [unchanged H (by omega),th]
  have retpath:=sweepR ret U (Mpos+1) (S-Mpos-1) (P:=P) (by omega) sret (by
    intro i lo hi
    rw [unchanged i (by omega)]
    obtain ⟨c,hc⟩:=source i (by omega) (by omega)
    rw [hc];exact rs c)
  rw [show Mpos+1+(S-Mpos-1)=S by omega] at retpath
  have arrive:=keep ret eSL S S U .stay (P:=P) (by omega) (by omega) sret (by rw [us];exact rn) rfl
  have four:=cross_right sl (show L ≤ P by omega) us ul (by
    intro i lo hi;rw [unchanged i (by omega)];exact reg i lo hi) cSL
  have five:=cross_right lh room ul uh (by
    intro i lo hi;rw [unchanged i (by omega)];exact beta i lo hi) cLH
  have whole:=one.append (two.append (three.append (a1.append (a2.append (retpath.append (arrive.append (four.append five)))))))
  convert whole using 1
  omega
end PhysicalCallerClosure
