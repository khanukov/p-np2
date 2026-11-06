import VirtualFinalClosure.GuardScan
namespace VirtualFinalClosure.GuardRestore
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",2),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","dispatch","dispatch",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","restore","restore",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row195_0","row195_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row196_0","row196_0",1),
      ("VirtualFinalClosure.GuardFinishRows","VirtualFinalClosure.GuardFinishRows","row196","row196",1),
      ("VirtualFinalClosure.GuardScan","VirtualFinalClosure.GuardScan","path","scanPath",1),
      ("VirtualFinalClosure.GuardScan","VirtualFinalClosure.GuardScan","metadata","scanMetadata",1),
      ("VirtualFinalClosure.GuardScan","VirtualFinalClosure.GuardScan","scanned","scanned",0),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","restored_bad","restoredBad",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","flag_preserved","flagPreserved",1),
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
private theorem eof (k P m S : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (mode : sourceMode m=2) (fit : S ≤ P) (blank : T S=none) :
    GPath (M:=machine k) P 1 (C k 194 m S T) (C k 231 m S T) := by
  exact keep (M:=machine k) (P:=P) (nc k 194 m) (nc k 231 m) S S T .stay fit fit
    (by rw [blank];simpa only [mode,if_pos rfl] using dispatch k m hm) rfl
/-- Restore the ACTUAL carried source cell, then physically check EVERY
remaining occupied source bit for zero, including both the active prefix and
inactive padding when the witness source is virtual. This is no rho shortcut. -/
private theorem live (k P m S h : Nat) (T : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (mode : sourceMode m=(if bits h then 1 else 0))
    (inside : h < S) (fit : S ≤ P) (endBlank : T S=none) (hole : T h=none)
    (suffix : ∀ j,h < j → j < S → T j=some (bits j)) :
    ∃ m',m' < 144 ∧ flag m'=flag m ∧
      (bad m'=0 ↔ bad m=0 ∧ ∀ j,h ≤ j → j < S → bits j=false) ∧
      GPath (M:=machine k) P (2*(S-h)+3) (C k 194 m S T)
        (C k 231 m' S (put T h (some (bits h)))) := by
  have occupied : sourceMode m≠2:=by rw [mode];cases bits h <;> decide
  have enter:=keep (M:=machine k) (P:=P) (nc k 194 m) (nc k 195 m) S S T .stay
    fit fit (by rw [endBlank];simpa only [if_neg occupied] using dispatch k m hm) rfl
  have left:=keep (M:=machine k) (P:=P) (nc k 195 m) (nc k 196 m) S (S-1) T .left
    fit (by omega) (by rw [endBlank];exact row195_0 k m hm) rfl
  have search:=sweepL (M:=machine k) (P:=P) (nc k 196 m) T h (S-h-1) (by omega) (by
    intro i lo hi
    rw [suffix i lo (by omega)]
    exact row196 k m hm (bits i))
  rw [show h+(S-h-1)=S-1 by omega] at search
  have found:=keep (M:=machine k) (P:=P) (nc k 196 m) (nc k 197 m) h h T .stay
    (by omega) (by omega) (by rw [hole];exact row196_0 k m hm) rfl
  have restored:=hop (M:=machine k) (P:=P) (nc k 197 m) (nc k 198 (changeMode 8 m)) h (h+1) T (some (bits h)) .right
    (by omega) (by omega) (by rw [hole];exact restore k m hm (bits h) mode) rfl
  let U:=put T h (some (bits h))
  have same (j : Nat) (lo : h < j) : U j=T j:=by dsimp only [U,put];rw [if_neg (by omega)]
  have scan:=scanPath k P (changeMode 8 m) (h+1) (S-h-1) U bits (modeBound _ _) (by omega)
    (by rw [show h+1+(S-h-1)=S by omega,same S inside,endBlank])
    (by intro j hj;rw [same _ (by omega)];exact suffix _ (by omega) (by omega))
  rw [show h+1+(S-h-1)=S by omega] at scan
  obtain ⟨mb,mf,_mm,clean⟩:=scanMetadata bits (changeMode 8 m) (h+1) (S-h-1) (modeBound _ _)
  refine ⟨scanned bits (changeMode 8 m) (h+1) (S-h-1),mb,mf.trans (flagPreserved 8 m hm),?_,?_⟩
  · rw [clean,restoredBad m hm (bits h) mode]
    constructor
    · rintro ⟨⟨old,first⟩,tail⟩
      refine ⟨old,?_⟩
      intro j lo hi
      by_cases hit : j=h
      · simpa only [hit] using first
      · have index : j=h+1+(j-h-1):=by omega
        rw [index]
        exact tail (j-h-1) (by omega)
    · rintro ⟨old,allBits⟩
      refine ⟨⟨old,allBits h le_rfl inside⟩,?_⟩
      intro j hj
      exact allBits (h+1+j) (by omega) (by omega)
  · have combined:=joinPath (joinPath (joinPath (joinPath (joinPath enter left) search) found) restored) scan
    rw [show 1+1+(S-h-1)+1+1+(S-h-1+1)=2*(S-h)+3 by omega] at combined
    exact combined
#print axioms eof
#print axioms live
end VirtualFinalClosure.GuardRestore
