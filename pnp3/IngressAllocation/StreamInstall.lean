import IngressAllocation.SmallPaths
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("SmallOrbit.Runtime","SmallOrbit","Frame","StreamFrame"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.full","fr_full"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.room","fr_room"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.source","fr_source"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.eof","fr_eof"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.reg","fr_reg"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.sep","fr_sep"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.marks","fr_marks"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.right","fr_right"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.hole","fr_hole"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.marker","fr_marker"),
      ("SmallOrbit.Runtime","SmallOrbit","stream_install_path","installPath"),
      ("SmallOrbit.Runtime","SmallOrbit","stream_read_path","readPath"),
      ("SmallOrbit.Runtime","SmallOrbit","install_read","installRead"),
      ("SmallOrbit.Runtime","SmallOrbit","Path.execute","pathRun"),
      ("IngressAllocation.SmallPaths","IngressAllocation.OrbitPrefix","every_head","pathHeads")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique physical Stream installation interface {mod}/{key}: {found.map Prod.fst}"
private theorem install_read_heads {N B S z n A F : Nat} (T : Nat → Option Bool)
    (frame : StreamFrame T S z n A F) (fit : F < tapeLength N B)
    (hL : S+z+2 < tapeLength N B) :
    ∀ u,u ≤ n+2+InputRead.readClock n z (S-A) → (Stream.machine.run u
      ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i=>T i.val⟩).head.val ≤ S+z+n+3 := by
  let L:=S+z+2
  let H:=S+z+n+3
  let U:=Body.clear T (S+z+3) n
  have low (i : Nat) (hi : i ≤ L) : U i=T i := by
    unfold U Body.clear;rw [if_neg (by dsimp only [L] at hi;omega)]
  have high (i : Nat) (hi : H ≤ i) : U i=T i := by
    unfold U Body.clear;rw [if_neg (by dsimp only [H] at hi;omega)]
  have digits (i : Nat) (lo : L < i) (hi : i < H) : U i=some false := by
    unfold U Body.clear;rw [if_pos (by dsimp only [L,H] at *;omega)]
  have src (i : Nat) (lo : A ≤ i) (hi : i < S) : ∃ b,U i=some b := by
    rw [low i (by dsimp only [L];omega)];exact (fr_source frame) i lo hi
  have eof : U S=none := by rw [low S (by dsimp only [L];omega)];exact (fr_eof frame)
  have reg (i : Nat) (lo : S < i) (hi : i < L) : U i=some false := by
    rw [low i (by omega)];exact (fr_reg frame) i lo hi
  have sep : U L=none := by rw [low L le_rfl];exact (fr_sep frame)
  have right : U H=none := by rw [high H le_rfl];exact (fr_right frame)
  have hole : U (A-2)=none := by rw [low _ (by have h:=(fr_full frame).2;dsimp only [L];omega)];exact (fr_hole frame)
  have marker : U (A-1)=some true := by rw [low _ (by have h:=(fr_full frame).2;dsimp only [L];omega)];exact (fr_marker frame)
  obtain ⟨mode,_virtual,_bit,path⟩:=readPath U A S z n (fr_full frame).1 (fr_full frame).2 hole marker src eof reg sep
    (by intro i lo hi;exact ⟨false,digits i lo hi⟩) right
  have hH : H < tapeLength N B:=(fr_room frame).trans fit
  have assoc : L+n+1=H := by dsimp only [L,H];omega
  have firstPath:=installPath T L n (fr_sep frame)
    (by intro i lo hi;rw [assoc] at hi;exact (fr_marks frame) i lo hi)
    (by rw [assoc];exact (fr_right frame))
  have installed:=pathRun (N:=N) (B:=B) firstPath (by rw [assoc];exact hH)
  have installed' : Stream.machine.run (n+2)
      ⟨Stream.machine.start,⟨L,hL⟩,fun i=>T i.val⟩=
      ⟨Stream.q 2,⟨H,hH⟩,fun i=>U i.val⟩ := by
    simpa only [assoc,show L+1=S+z+3 from rfl,U] using installed
  have firstHeads:=pathHeads firstPath (by rw [assoc];exact hH) hL
  have secondHeads:=pathHeads path hH hH
  intro u hu
  by_cases early : u ≤ n+2
  · exact (firstHeads u early).trans (Nat.le_of_eq assoc)
  · rw [show u=n+2+(u-(n+2)) by omega,UniformTM.run_add,installed']
    exact secondHeads (u-(n+2)) (by omega)
end IngressAllocation
