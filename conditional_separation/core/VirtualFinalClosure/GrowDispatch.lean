import VirtualFinalClosure.MarkerEnd
namespace VirtualFinalClosure.GrowDispatch
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual growing-bank path interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank path interface {mod}/{key}"
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","keep_to_paid","keepToPaid",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row41_0","row41",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row42_0","row42end",1),
      ("VirtualFinalClosure.NativeRoutes","VirtualFinalClosure.NativeRoutes","row42","row42",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","resolved_row","resolvedRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","resolve","resolveCode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong native marked-source dispatch term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique native marked-source dispatch term {mod}/{key}"
private theorem grow_row (k m : Nat) (hm : m < 144) (observed : seen m=1) :
    (machine k).step (nc k 40 m) none=(nc k 41 m,none,.stay) := by
  have resolve : resolveCode k 242 (changeMeta 0 m)=
      (CertificateGuardClosure.machine k).stateCount+41 := by
    rw [mode0 m hm]
    change _+(if seen m=1 then 41 else 50)=_
    rw [if_pos observed]
  have row:=resolvedRow k 40 m 242 41 0 1 0 none (by decide) hm
    (by run_tac cellTac 120) resolve
  rw [mode0 m hm] at row
  exact row
/-- The physical suffix has a real observed true; native40 selects actual
capacity growth and traverses the ORIGINAL source suffix to the old workspace.
This fact does not decide original rho or the BE active index. -/
private theorem to_reset (k P m S L H Q F p : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (observed : seen m=1) (fr : Frame T S L H Q F)
    (gap : H+Q+1 < F) (fit : F+1 ≤ P) (inside : p < S) (hole : T p=none)
    (suffix : ∀ i,p < i → i < S → ∃ b,T i=some b) :
    GPath (M:=machine k) P (F-p+5) (C k 40 m p T) (C k 52 m (F+1) T) := by
  have frameCopy:=fr
  obtain ⟨sl,lh,qp,arena,sourceEnd,_l,_h,_d0,_f,_reg,_assign,_marks,_gap⟩:=frameCopy
  have room : S ≤ F+1 := by omega
  have dispatch:=keep (M:=machine k) (P:=P) (nc k 40 m) (nc k 41 m) p p T .stay
    (by omega) (by omega) (by rw [hole];exact grow_row k m hm observed) rfl
  have enter:=keep (M:=machine k) (P:=P) (nc k 41 m) (nc k 42 m) p (p+1) T .right
    (by omega) (by omega) (by rw [hole];exact row41 k m hm) rfl
  have scan:=sweepR (M:=machine k) (P:=P) (nc k 42 m) T (p+1) (S-p-1) (by omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=suffix i (by omega) (by omega)
    rw [cell];exact row42 k m hm b)
  rw [show p+1+(S-p-1)=S by omega] at scan
  have exit:=keep (M:=machine k) (P:=P) (nc k 42 m) (nc k 43 m) S S T .stay
    (by omega) (by omega) (by rw [sourceEnd];exact row42end k m hm) rfl
  have route:=keepToPaid k P m S L H Q F T hm fr gap fit
  have path:=joinPath (joinPath (joinPath (joinPath dispatch enter) scan) exit) route
  convert path using 1;omega
#print axioms grow_row
#print axioms to_reset
end VirtualFinalClosure.GrowDispatch
