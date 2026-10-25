import FullIngressClosure.FinishPrepared
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena","Arena"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.gap","arenaGap"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor","Corridor"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.order","corridorOrder"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_corridor","bankCorridor"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_arena","bankArena"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","bank_below","bankBelow"),
      ("FullIngressClosure.FinishPrepared","FullIngressClosure","bank_exterior","bankExterior") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique preserved physical environment term {mod}/{key}: {found.map Prod.fst}"
private structure Environment (D : Nat → Nat) (original T : Nat → Option Bool)
    (S L H F Q p : Nat) (source : Fin S → Bool) : Prop where
  d0 : D 0=F+1
  corridor : Corridor T S L H
  arena : Arena T H F Q
  sourceCells : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)
  exterior : ∀ i,i < D 0 ∨ D 12 < i → T i=original i
private theorem environment_bank {D original T S L H F Q p source}
    (frame : Environment D original T S L H F Q p source) (grid : Grid D T)
    (j v : Nat) (hj : j < 12) : Environment D original (setBank T D j v) S L H F Q p source := by
  have order:=corridorOrder frame.corridor
  have gap:=arenaGap frame.arena
  have d0:=frame.d0
  refine ⟨frame.d0,bankCorridor grid frame.corridor hj (by omega) (v:=v),bankArena grid frame.arena hj frame.d0 (v:=v),?_,?_⟩
  · intro i il iu
    rw [bankBelow grid (j:=j) (v:=v) (i:=i) hj (by omega)]
    exact frame.sourceCells i il iu
  · intro i hi
    rw [bankExterior grid T j v i hj hi]
    exact frame.exterior i hi
end FullIngressClosure
