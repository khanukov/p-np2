import PhysicalCallerClosure.TableReadRows
import PhysicalCallerClosure.TableSeek
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","put","keep","hop","dest","ns","NativeSafe"]),
      (`PhysicalCallerClosure.SourcePrepare,["CrossRows","cross_left"]),
      (`PhysicalCallerClosure.TableSeek,["TableSeekRows","seek_table"]),
      (`PhysicalCallerClosure.TableRead,["TableReadRows","read_table"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def PlainSeekRows (entry out : Fin M.stateCount) : Prop :=
  ∃ eL eS:Fin M.stateCount,CrossRows (Safe:=Safe) .left entry eL ∧
    CrossRows (Safe:=Safe) .left eL eS ∧ CrossRows (Safe:=Safe) .left eS out
private theorem plain_seek {P p S L H T entry out} (ps:p < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (tp:T p=none) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,p < i → i < S → ∃ b,T i=some b)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b) (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (code:PlainSeekRows (Safe:=Safe) entry out) :
    Path M Safe P (H-p+3) (node entry H T) (node out p T) := by
  obtain ⟨eL,eS,cl,cs,cp⟩:=code
  have a:=cross_left lh room tl th beta cl
  have b:=cross_left sl (show L ≤ P by omega) ts tl reg cs
  have c:=cross_left ps (show S ≤ P by omega) tp ts source cp
  have whole:=a.append (b.append c)
  convert whole using 1
  omega
private structure ShiftRows (anchored : Bool) (b : Bool) (entry : Fin M.stateCount) (out : Fin 3 → Fin M.stateCount) where
  restore : Fin M.stateCount
  read : Fin M.stateCount
  seek : if anchored then Nonempty (TableSeekRows (Safe:=Safe) entry restore) else PlainSeekRows (Safe:=Safe) entry restore
  safeRestore : Safe restore
  write : M.step restore none=(read,some b,.right)
  next : TableReadRows (Safe:=Safe) anchored read out
private theorem shift_table {P p anchor S L H T anchored b entry out}
    (ps:p < S) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (tp:T p=none) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (source:∀ i,p < i → i < S → (anchored=false ∨ i≠anchor) → ∃ c,T i=some c)
    (anchorFrame:anchored=true → p+1 < anchor ∧ anchor < S ∧ T anchor=none)
    (reg:∀ i,S < i → i < L → ∃ c,T i=some c) (beta:∀ i,L < i → i < H → ∃ c,T i=some c)
    (code:ShiftRows (Safe:=Safe) anchored b entry out) :
    ∃ tag:Fin 3,(tag.val=2 ↔ p+1=S) ∧ (tag.val=1 ↔ T (p+1)=some true) ∧
      Path M Safe P (2*(H-p)+(if anchored then 7 else 6)) (node entry H T)
        (node (out tag) H (put (put T p (some b)) (p+1) none)) := by
  have seek:Path M Safe P (H-p+(if anchored then 4 else 3)) (node entry H T) (node code.restore p T):=by
    by_cases h:anchored=true
    · have codes:=code.seek
      rw [if_pos h] at codes
      obtain ⟨sc⟩:=codes
      obtain ⟨pa,as,ah⟩:=anchorFrame h
      simpa only [if_pos h] using seek_table (by omega) as sl lh room tp ah ts tl th (by
        intro i lo hi ne;exact source i lo hi (Or.inr ne)) reg beta sc
    · have h0:anchored=false:=by cases anchored <;> simp_all
      have codes:=code.seek
      rw [if_neg h] at codes
      simpa only [if_neg h] using plain_seek ps sl lh room tp ts tl th (by
        intro i lo hi;exact source i lo hi (Or.inl h0)) reg beta codes
  have w:=hop code.restore code.read p (p+1) T (some b) .right (P:=P) (by omega) (by omega) code.safeRestore
    (by rw [tp];exact code.write) rfl
  let U:=put T p (some b)
  have high (i) (hi:p < i) : U i=T i:=by simp only [U,put,if_neg (show i≠p by omega)]
  obtain ⟨tag,te,tv,path⟩:=read_table (T:=U) (anchor:=anchor) (show p+1 ≤ S by omega) sl lh room
    (by rw [high S ps];exact ts) (by rw [high L (by omega)];exact tl) (by rw [high H (by omega)];exact th)
    (by intro i lo hi ne;rw [high i (by omega)];exact source i (by omega) hi ne)
    (by intro phy;rw [high (p+1) (by omega)];by_cases h:anchored=true
        · have pa:=(anchorFrame h).1;exact source (p+1) (by omega) phy (Or.inr (by omega))
        · have h0:anchored=false:=by cases anchored <;> simp_all
          exact source (p+1) (by omega) phy (Or.inl h0))
    (by intro _ h;obtain ⟨pa,as,ah⟩:=anchorFrame h;exact ⟨pa,as,by rw [high anchor (by omega)];exact ah⟩)
    (by intro i lo hi;rw [high i (by omega)];exact reg i lo hi)
    (by intro i lo hi;rw [high i (by omega)];exact beta i lo hi) code.next
  refine ⟨tag,te,?_,?_⟩
  · simpa only [high (p+1) (by omega)] using tv
  · have whole:=seek.append (w.append path)
    convert whole using 1
    by_cases h:anchored=true
    · simp only [if_pos h];omega
    · simp only [if_neg h];omega
end PhysicalCallerClosure
