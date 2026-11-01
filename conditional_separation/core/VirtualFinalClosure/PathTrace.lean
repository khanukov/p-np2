import VirtualFinalClosure.Paths
namespace VirtualFinalClosure.PathTrace
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName,kind) in [
      ("Node","GNode",(2:Nat)),("Path","GPath",2),("Path.nil","nilPath",3),
      ("Path.cons","consPath",3),("Edge.before","edgeBefore",1),("Path.bounds","bounds",1),
      ("Path.execute","execute",1),("embed","embed",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith "_private.SmallIngress.Runtime." &&
      n.toString.endsWith (".SmallIngress."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong existing physical path interface {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique same-allocation path trace term {key}"
/-- Prefix closure of the EXISTING path type. No new path engine or observer. -/
private theorem path_prefix {M : UniformTM} {P t : Nat} {c d : GNode M}
    (path : GPath (M:=M) P t c d) (u : Nat) (hu : u≤t) :
    ∃ e : GNode M,GPath (M:=M) P u c e := by
  induction path generalizing u with
  | nil c fit=>
    have zero : u=0 := by omega
    subst u
    exact ⟨c,nilPath c fit⟩
  | cons edge tail ih=>
    cases u with
    | zero=>exact ⟨_,nilPath _ (edgeBefore edge)⟩
    | succ u=>
      obtain ⟨e,pre⟩:=ih u (by omega)
      exact ⟨e,consPath edge pre⟩
/-- Every actual finite-budget microstep has the SAME explicit head footprint;
this statement makes no comparison between elapsed time and tape allocation. -/
private theorem through {M : UniformTM} {N B P t : Nat} {c d : GNode M}
    (path : GPath (M:=M) P t c d) (fit : P<tapeLength N B) :
    ∀ u,u≤t →
      (M.run u (embed c (lt_of_le_of_lt (bounds path).1 fit))).head.val≤P := by
  intro u hu
  obtain ⟨e,pre⟩:=path_prefix path u hu
  have done:=execute (N:=N) (B:=B) pre fit
  rw [done]
  exact (bounds pre).2
#print axioms path_prefix
#print axioms through
end VirtualFinalClosure.PathTrace
