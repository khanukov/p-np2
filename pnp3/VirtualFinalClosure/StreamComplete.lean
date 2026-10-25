import VirtualFinalClosure.StreamInitPrepared
import VirtualFinalClosure.StreamActiveOrbit
namespace VirtualFinalClosure.StreamComplete
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallOrbit.Runtime","SmallOrbit","Frame","Frame",(2:Nat)),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.full","fr_full",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.room","fr_room",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.source","fr_source",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.eof","fr_eof",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.reg","fr_reg",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.sep","fr_sep",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.marks","fr_marks",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.right","fr_right",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.scratch","fr_scratch",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.fence","fr_fence",1),
      ("Stream.Kernel","Stream","Arena","Arena",2),
      ("Stream.Kernel","Stream","Arena.mk","arenaMk",3),
      ("VirtualFinalClosure.StreamInitPrepared","VirtualFinalClosure.StreamInitPrepared","prepared","initial",1),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","complete_orbit","orbit",1),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","entry","entry",0),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","ended","ended",0),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","widen","widen",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","append",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong complete native Stream component term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique complete native Stream component term {mod}/{key}"
/-- Literal assignment installation, first read, and EVERY paid native carry
round on one table. Each row changes the finite flag on its unique paid edge;
all other native phases preserve it. No host assignment array is used. -/
private theorem prepared (k S z n A F : Nat) (T : Nat → Option Bool)
    (frame : Frame T S z n A F) (cap : 2^n≤F-(S+z+n+3)-1) :
    let U:=Body.clear T (S+z+3) n
    ∃ t,t≤n+2+InputRead.readClock n z (S-A)+(2^n)*(8*F+16) ∧
      GPath (M:=machine k) F t (node (q k ⟨1,by decide⟩ 0) (S+z+2) T)
        (ended k U S z n A (2^n)):=by
  intro U
  let H:=S+z+n+3
  have low (i : Nat) (hi : i≤S+z+2) : U i=T i:=by
    dsimp only [U,Body.clear];rw [if_neg (by omega)]
  have high (i : Nat) (hi : H≤ i) : U i=T i:=by
    dsimp only [U,Body.clear];rw [if_neg (by dsimp only [H] at hi;omega)]
  have arena : Arena U S z n A F:=by
    refine arenaMk (fr_full frame).2 (fr_room frame) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i lo hi
      rw [low i (by omega)]
      exact fr_source frame i lo hi
    · rw [low S (by omega)];exact fr_eof frame
    · intro i lo hi;rw [low i (by omega)];exact fr_reg frame i lo hi
    · rw [low _ le_rfl];exact fr_sep frame
    · rw [high H le_rfl];exact fr_right frame
    · intro i lo hi;rw [high i lo.le];exact fr_scratch frame i lo hi
    · rw [high F (by have h:=fr_room frame;omega)];exact fr_fence frame
  have first:=initial k S z n A F ⟨1,by decide⟩ T frame
  have cur0 : Stream.Target.cursor A S 0=A:=by
    dsimp only [Stream.Target.cursor]
    rw [Nat.add_zero,Nat.min_eq_left (fr_full frame).2]
  have startEq : entry k U S z n A 0=
      node (q k ⟨1,by decide⟩ (11+8*(Stream.Target.mode U A S).val)) H
        (Stream.Target.image U S z n A 0 0 true):=by
    dsimp only [entry,folded]
    rw [cur0]
    rfl
  obtain ⟨u,up,rest⟩:=orbit k U S z n A F arena cap
  rw [startEq] at rest
  refine ⟨(n+2+InputRead.readClock n z (S-A))+u,by omega,?_⟩
  exact append (widen first (Nat.le_of_lt (fr_room frame))) rest
#print axioms prepared
end VirtualFinalClosure.StreamComplete
