import VirtualFinalClosure.StreamInitPaths
import VirtualFinalClosure.StreamDrawPaths
import SmallOrbit.Runtime
namespace VirtualFinalClosure.StreamInitPrepared
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
      ("SmallOrbit.Runtime","SmallOrbit","Frame.hole","fr_hole",1),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.marker","fr_marker",1),
      ("VirtualFinalClosure.StreamInitPaths","VirtualFinalClosure.StreamInitPaths","install_path","install",1),
      ("VirtualFinalClosure.StreamInitPaths","VirtualFinalClosure.StreamInitPaths","seek_path","seek",1),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","read_draw","readDraw",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","unpaid","unpaid",0),
      ("Stream.Kernel","Stream","draw_zero","drawZero",1),
      ("Stream.Kernel","Stream","image_draw","imageDraw",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","append",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual Stream first-read frame {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual Stream first-read frame {mod}/{key}"
/-- Actual unary assignment installation, cursor discovery and first lift on
this active table. Its flag is constant until the paid observation edge. -/
private theorem prepared (k S z n A F : Nat) (f : Fin 4) (T : Nat → Option Bool)
    (frame : Frame T S z n A F) :
    let U:=Body.clear T (S+z+3) n
    GPath (M:=machine k) (S+z+n+3) (n+2+InputRead.readClock n z (S-A))
      (node (q k f 0) (S+z+2) T)
      (node (unpaid k f (Stream.Target.mode U A S)) (S+z+n+3)
        (Stream.Target.image U S z n A 0 0 true)):=by
  intro U
  let L:=S+z+2
  let H:=S+z+n+3
  have low (i : Nat) (hi : i≤L) : U i=T i:=by
    dsimp only [U,Body.clear]
    rw [if_neg (by dsimp only [L] at hi;omega)]
  have high (i : Nat) (hi : H≤ i) : U i=T i:=by
    dsimp only [U,Body.clear]
    rw [if_neg (by dsimp only [H] at hi;omega)]
  have digits (i : Nat) (lo : L < i) (hi : i < H) : U i=some false:=by
    dsimp only [U,Body.clear]
    rw [if_pos (by dsimp only [L,H] at lo hi;omega)]
  have source (i : Nat) (lo : A≤ i) (hi : i < S) : ∃ b,U i=some b:=by
    rw [low i (by dsimp only [L];omega)]
    exact fr_source frame i lo hi
  have eof : U S=none:=by rw [low S (by dsimp only [L];omega)];exact fr_eof frame
  have reg (i : Nat) (lo : S < i) (hi : i < L) : U i=some false:=by
    rw [low i (by omega)];exact fr_reg frame i lo hi
  have sep : U L=none:=by rw [low L le_rfl];exact fr_sep frame
  have right : U H=none:=by rw [high H le_rfl];exact fr_right frame
  have hole : U (A-2)=none:=by
    rw [low _ (by have h:=(fr_full frame).2;dsimp only [L];omega)]
    exact fr_hole frame
  have marker : U (A-1)=some true:=by
    rw [low _ (by have h:=(fr_full frame).2;dsimp only [L];omega)]
    exact fr_marker frame
  have assoc : L+n+1=H:=by dsimp only [L,H];omega
  have installed:=install k f T L n (fr_sep frame)
    (by intro i lo hi;rw [assoc] at hi;exact fr_marks frame i lo hi)
    (by rw [assoc];exact fr_right frame)
  rw [assoc,show L+1=S+z+3 from rfl] at installed
  have cursor:=seek k f U A S z n (fr_full frame).1 (fr_full frame).2 hole marker source eof reg sep
    (by intro i lo hi;exact ⟨false,digits i lo hi⟩) right
  have read:=readDraw k f U S z n A 0 (List.replicate n false) (fr_full frame).2 source eof reg sep right
  rw [drawZero U S z n A digits] at read
  have cur0 : Stream.Target.cursor A S 0=A:=by
    dsimp only [Stream.Target.cursor];rw [Nat.add_zero,Nat.min_eq_left (fr_full frame).2]
  have target:=imageDraw U S z n A 0 0 true
  rw [cur0] at target
  dsimp only [Body.iterBits] at target
  rw [←target] at read
  have path:=append (append installed cursor) read
  convert path using 1
  dsimp only [InputRead.readClock]
  omega
#print axioms prepared
end VirtualFinalClosure.StreamInitPrepared
