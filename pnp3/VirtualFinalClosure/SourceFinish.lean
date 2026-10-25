import VirtualFinalClosure.NativeRoutes
import VirtualFinalClosure.SourceLoop
namespace VirtualFinalClosure.SourceFinish
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","resolved_row","resolvedRow",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","carried_write","carriedWrite",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row38_0","r38",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row39_0","r39none",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row39","r39",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row41_0","r41",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row42_0","r42none",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row42","r42",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row51_0","r51none",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row51","r51",1)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual source-finish declaration {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical source-finish interface {mod}/{key}"
private theorem final_hole (k P m S p : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (physical : p < S) (fit : S ≤ P)
    (sourceEnd : T S=none) (hole : T p=none)
    (suffix : ∀ i,p < i → i < S → ∃ b,T i=some b) :
    GPath (M:=machine k) P (S-p+1) (C k 38 m S T) (C k 40 m p T) := by
  have enter:=keep (M:=machine k) (P:=P) (nc k 38 m) (nc k 39 m) S (S-1) T .left
    fit (by omega) (by rw [sourceEnd];exact r38 k m hm) rfl
  have scan:=sweepL (M:=machine k) (P:=P) (nc k 39 m) T p (S-p-1) (by omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=suffix i lo (by omega)
    rw [cell];exact r39 k m hm b)
  rw [show p+(S-p-1)=S-1 by omega] at scan
  have finish:=keep (M:=machine k) (P:=P) (nc k 39 m) (nc k 40 m) p p T .stay
    (by omega) (by omega) (by rw [hole];exact r39none k m hm) rfl
  have path:=joinPath (joinPath enter scan) finish
  rw [show 1+(S-p-1)+1=S-p+1 by omega] at path
  exact path
private theorem row40 (k m : Nat) (hm : m < 144) :
    (machine k).step (nc k 40 m) none=(nc k (if seen m=1 then 41 else 50) m,none,.stay) := by
  have resolution : resolveCode k 242 (changeMeta 0 m)=
      (CertificateGuardClosure.machine k).stateCount+(if seen m=1 then 41 else 50) := by
    rw [mode0 m hm]
    rfl
  have row:=resolvedRow k 40 m 242 (if seen m=1 then 41 else 50) 0 1 0 none
    (by decide) hm (by run_tac cellTac 120) resolution
  rw [mode0 m hm] at row
  exact row
private theorem dispatch (k P m p : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : p ≤ P) (hole : T p=none) :
    GPath (M:=machine k) P 1 (C k 40 m p T) (C k (if seen m=1 then 41 else 50) m p T) := by
  exact keep (M:=machine k) (P:=P) (nc k 40 m) (nc k (if seen m=1 then 41 else 50) m)
    p p T .stay fit fit (by rw [hole];exact row40 k m hm) rfl
private theorem keep_hole (k P m S p : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (physical : p < S) (fit : S ≤ P)
    (sourceEnd : T S=none) (hole : T p=none)
    (suffix : ∀ i,p < i → i < S → ∃ b,T i=some b) :
    GPath (M:=machine k) P (S-p+1) (C k 41 m p T) (C k 43 m S T) := by
  have enter:=keep (M:=machine k) (P:=P) (nc k 41 m) (nc k 42 m) p (p+1) T .right
    (by omega) (by omega) (by rw [hole];exact r41 k m hm) rfl
  have scan:=sweepR (M:=machine k) (P:=P) (nc k 42 m) T (p+1) (S-p-1) (by omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=suffix i (by omega) (by omega)
    rw [cell];exact r42 k m hm b)
  rw [show p+1+(S-p-1)=S by omega] at scan
  have finish:=keep (M:=machine k) (P:=P) (nc k 42 m) (nc k 43 m) S S T .stay
    fit fit (by rw [sourceEnd];exact r42none k m hm) rfl
  have path:=joinPath (joinPath enter scan) finish
  rw [show 1+(S-p-1)+1=S-p+1 by omega] at path
  exact path
private theorem row50 (k m : Nat) (b : Bool) (hm : m < 144)
    (mode : sourceMode m=(if b then 1 else 0)) :
    (machine k).step (nc k 50 m) none=(nc k 51 m,some b,.right) := by
  have row:=literalRow k 50 m 51 3 2 0 none (by decide) hm (by decide) (by run_tac cellTac 150)
  rw [mode0 m hm,carriedWrite m b mode] at row
  exact row
private theorem restore_hole (k P m S p : Nat) (T : Nat → Option Bool) (b : Bool)
    (hm : m < 144) (physical : p < S) (fit : S ≤ P)
    (mode : sourceMode m=(if b then 1 else 0)) (sourceEnd : T S=none) (hole : T p=none)
    (suffix : ∀ i,p < i → i < S → ∃ bit,T i=some bit) :
    GPath (M:=machine k) P (S-p+1) (C k 50 m p T)
      (C k 231 m S (put T p (some b))) := by
  have enter:=hop (M:=machine k) (P:=P) (nc k 50 m) (nc k 51 m) p (p+1) T (some b) .right
    (by omega) (by omega) (by rw [hole];exact row50 k m b hm mode) rfl
  let U:=put T p (some b)
  have scan:=sweepR (M:=machine k) (P:=P) (nc k 51 m) U (p+1) (S-p-1) (by omega) (by
    intro i lo hi
    obtain ⟨bit,cell⟩:=suffix i (by omega) (by omega)
    have unchanged : U i=T i := by dsimp only [U,put];rw [if_neg (by omega)]
    rw [unchanged,cell];exact r51 k m hm bit)
  rw [show p+1+(S-p-1)=S by omega] at scan
  have endBlank : U S=none := by dsimp only [U,put];rw [if_neg (by omega),sourceEnd]
  have finish:=keep (M:=machine k) (P:=P) (nc k 51 m) (nc k 231 m) S S U .stay
    fit fit (by rw [endBlank];exact r51none k m hm) rfl
  have path:=joinPath (joinPath enter scan) finish
  rw [show 1+(S-p-1)+1=S-p+1 by omega] at path
  exact path
#print axioms final_hole
#print axioms row40
#print axioms dispatch
#print axioms keep_hole
#print axioms restore_hole
end VirtualFinalClosure.SourceFinish
