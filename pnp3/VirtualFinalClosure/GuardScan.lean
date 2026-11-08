import VirtualFinalClosure.GuardFinishRows
namespace VirtualFinalClosure.GuardScan
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","scan","scanRow",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row198_0","endRow",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","flag_preserved","flagPreserved",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","mode_preserved","modePreserved",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","scan_bad","scanBad",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","modeBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
/-- Proof-side record of the ACTUAL finite-state bad-bit updates. This is
never an input operand of rawStep and writes no cells. -/
private def scanned (bits : Nat → Bool) : Nat → Nat → Nat → Nat
  | m,_,0=>m
  | m,h,count+1=>scanned bits (changeMode (if bits h then 5 else 0) m) (h+1) count
private def scanned_type : (Nat → Bool) → Nat → Nat → Nat → Nat:=scanned
private theorem metadata (bits : Nat → Bool) (m h count : Nat) (hm : m < 144) :
    scanned bits m h count < 144 ∧ flag (scanned bits m h count)=flag m ∧
      sourceMode (scanned bits m h count)=sourceMode m ∧
      (bad (scanned bits m h count)=0 ↔ bad m=0 ∧ ∀ j,j < count → bits (h+j)=false) := by
  induction count generalizing m h with
  | zero=>
    refine ⟨hm,rfl,rfl,?_⟩
    simp only [scanned,Nat.not_lt_zero,IsEmpty.forall_iff,implies_true,and_true]
  | succ count ih=>
    let op:=if bits h then 5 else 0
    let next:=changeMode op m
    obtain ⟨nb,nf,nm,clean⟩:=ih next (h+1) (modeBound op m)
    have which : op=0 ∨ op=5 ∨ op=7 ∨ op=8:=by dsimp only [op];split <;> simp only [or_true,true_or]
    refine ⟨nb,nf.trans (flagPreserved op m hm),nm.trans (modePreserved op m hm which),?_⟩
    change bad (scanned bits next (h+1) count)=0 ↔ _
    rw [clean,scanBad m hm (bits h)]
    constructor
    · rintro ⟨⟨old,first⟩,rest⟩
      refine ⟨old,?_⟩
      intro j hj
      cases j with
      | zero=>simpa only [Nat.add_zero] using first
      | succ j=>simpa only [Nat.add_assoc,Nat.add_comm 1 j] using rest j (by omega)
    · rintro ⟨old,allBits⟩
      refine ⟨⟨old,by simpa only [Nat.add_zero] using allBits 0 (by omega)⟩,?_⟩
      intro j hj
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using allBits (j+1) (by omega)
/-- Full native physical zero scan; FALSE is occupied data, not EOF. Exactly
one actual cell observation per source cell and a final literal EOF stay. -/
private theorem path (k P m h count : Nat) (T : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (fit : h+count ≤ P) (last : T (h+count)=none)
    (source : ∀ j,j < count → T (h+j)=some (bits (h+j))) :
    GPath (M:=machine k) P (count+1) (C k 198 m h T)
      (C k 231 (scanned bits m h count) (h+count) T) := by
  induction count generalizing m h with
  | zero=>
    simpa only [scanned,Nat.add_zero] using
      (keep (M:=machine k) (P:=P) (nc k 198 m) (nc k 231 m) h h T .stay
        (by omega) (by omega) (by rw [show T h=none by simpa only [Nat.add_zero] using last];exact endRow k m hm) rfl)
  | succ count ih=>
    let next:=changeMode (if bits h then 5 else 0) m
    have first:=keep (M:=machine k) (P:=P) (nc k 198 m) (nc k 198 next) h (h+1) T .right
      (by omega) (by omega) (by
        rw [show T h=some (bits h) by simpa only [Nat.add_zero] using source 0 (by omega)]
        exact scanRow k m hm (bits h)) rfl
    have rest:=ih next (h+1) (modeBound _ _) (by omega)
      (by simpa only [Nat.add_assoc,Nat.add_comm 1 count] using last)
      (by intro j hj;simpa only [Nat.add_assoc,Nat.add_comm 1 j] using source (j+1) (by omega))
    have combined:=joinPath first rest
    simpa only [scanned,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,next] using combined
#print axioms scanned_type
#print axioms metadata
#print axioms path
end VirtualFinalClosure.GuardScan
