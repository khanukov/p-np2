import FullIngressClosure.FinishCertificates
import FullIngressClosure.FinalImage
import FullIngressClosure.Registers
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("FullIngressClosure.Registers","FullIngressClosure","Registers","Registers"),
      ("FullIngressClosure.Registers","FullIngressClosure","Registers.mk","registersMk"),
      ("FullIngressClosure.Registers","FullIngressClosure","Registers.grid","registerGrid"),
      ("FullIngressClosure.Registers","FullIngressClosure","Registers.unary","registerUnary"),
      ("FullIngressClosure.Registers","FullIngressClosure","registers_set","registersSet"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.Workspace","FullIngressClosure","bank_grid","bankGrid"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena","Arena"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.gap","arenaGap"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor","Corridor"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.order","corridorOrder"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted","lifted"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_lifted","bankLifted"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted_grid","liftedGrid"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted_arena","liftedArena"),
      ("FullIngressClosure.FinishStage","FullIngressClosure","finish_stage","finishStage"),
      ("FullIngressClosure.FinishCertificates","FullIngressClosure","finishState","finishState"),
      ("FullIngressClosure.FinishCertificates","FullIngressClosure","finishCases","finishCases"),
      ("FullIngressClosure.FinalImage","FullIngressClosure","endpointValues","endpointValues"),
      ("FullIngressClosure.FinalImage","FullIngressClosure","complete_image","completeImage"),
      ("FullIngressClosure.FinalImage","FullIngressClosure","lifted_prepared","liftedPrepared") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique exact prepared finish proof {mod}/{key}: {found.map Prod.fst}"
private def endValues (n g W anchor residue9 residue11 j : Nat) : Nat :=
  if j=0 ∨ j=6 then g else if j=2 then bitLength n else if j=3 ∨ j=4 then W
  else if j=7 then anchor else if j=9 then residue9 else if j=11 then residue11 else 0
private theorem cleared_registers {D T r n g W anchor residue9 residue11}
    (frame : Registers D T (endValues n g W anchor residue9 residue11)) :
    Registers D (setBank (setBank (setBank T D 9 0) D 11 0) D 10 (3*r+3))
      (endpointValues r n g W anchor) := by
  have done:=registersSet (registersSet (registersSet frame 9 0 (by decide)) 11 0 (by decide)) 10 (3*r+3) (by decide)
  refine registersMk (registerGrid done) ?_
  intro j hj
  have h:=registerUnary done j hj
  have eq : Function.update (Function.update (Function.update (endValues n g W anchor residue9 residue11) 9 0) 11 0) 10 (3*r+3) j=
      endpointValues r n g W anchor j:=by interval_cases j <;> rfl
  rwa [eq] at h
private theorem bank_exterior {D T} (grid : Grid D T) (U : Nat → Option Bool) (j v i : Nat)
    (hj : j < 12) (outside : i < D 0 ∨ D 12 < i) : setBank U D j v i=U i := by
  have avoid : ¬(D j < i ∧ i < D (j+1)):=by
    rcases outside with low | high
    · have h:=gridMono grid 0 j (by omega) (by omega); omega
    · have h:=gridMono grid (j+1) 12 (by omega) le_rfl; omega
  dsimp only [setBank]
  rw [if_neg avoid]
private theorem finish_prepared {k lo P S L H F r n g W M residue9 residue11 Q}
    (source : Fin S → Bool) (original U : Nat → Option Bool)
    (frame : Registers (SerializedBody.delimiter F r n) U
      (endValues n g W (S-min M S) residue9 residue11))
    (corridor : Corridor U S L H) (arena : Arena U H F Q)
    (outside : ∀ i,i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i → U i=original i)
    (lower : lo ≤ H) (upper : SerializedBody.delimiter F r n 12 ≤ P) :
    ∃ t,t ≤ 32*(P+16) ∧ PPath k lo P t
      (pNode (finishState k (SerializedBody.sourceMode source M)) (SerializedBody.delimiter F r n 0) (lifted U S (min M S)))
      (pNode (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))) H
        (SerializedBody.prepared original S M F r n g W)) := by
  let D:=SerializedBody.delimiter F r n
  let q:=min M S
  let E:=setBank (setBank (setBank U D 9 0) D 11 0) D 10 (3*r+3)
  have grid:=registerGrid frame
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  have below : S < D 0:=by change S < F+1; omega
  have qs : q ≤ S:=Nat.min_le_right _ _
  have holeGrid:=liftedGrid grid below qs
  have holeArena:=liftedArena arena (by omega : S < H) qs
  have len9 : D 10=D 9+2*r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have len11 : D 12=D 11+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have len10 : D 11=D 10+(3*r+3)+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  obtain ⟨t,price,path⟩:=finishStage (k:=k) (lo:=lo) (P:=P) (finishCases k (SerializedBody.sourceMode source M))
    holeGrid holeArena rfl (2*r) r (3*r+3) len9 len11 len10 lower upper
  have mask : setBank (setBank (setBank (lifted U S q) D 9 0) D 11 0) D 10 (3*r+3)=lifted E S q := by
    rw [bankLifted grid below qs (by decide),
      bankLifted (bankGrid grid 9 0 (by decide)) below qs (by decide),
      bankLifted (bankGrid (bankGrid grid 9 0 (by decide)) 11 0 (by decide)) below qs (by decide)]
  rw [mask] at path
  have finalFrame:=cleared_registers (r:=r) frame
  have exterior (i : Nat) (hi : i < D 0 ∨ D 12 < i) : E i=original i:=by
    change setBank (setBank (setBank U D 9 0) D 11 0) D 10 (3*r+3) i=original i
    rw [bank_exterior grid _ 10 (3*r+3) i (by decide) hi,
      bank_exterior grid _ 11 0 i (by decide) hi,bank_exterior grid _ 9 0 i (by decide) hi]
    exact outside i hi
  have image : E=SerializedBody.image original F r n g W (S-min M S) 0 0 W g:=
    completeImage F r n g W (S-min M S) original E (registerGrid finalFrame) (registerUnary finalFrame) exterior
  rw [image] at path
  rw [liftedPrepared original S M F r n g W] at path
  exact ⟨t,price,path⟩
end FullIngressClosure
