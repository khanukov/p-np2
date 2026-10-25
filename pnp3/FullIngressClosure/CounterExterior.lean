import FullIngressClosure.CounterFront
import FullIngressClosure.SourceImage
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("FullIngressClosure.CounterFront","FullIngressClosure","counterTape","counterTape"),
      ("FullIngressClosure.ArithmeticStage","FullIngressClosure","arithmeticTape","arithmeticTape"),
      ("FullIngressClosure.HalfDriver","FullIngressClosure","halfPhase","halfPhase"),
      ("FullIngressClosure.Move","FullIngressClosure","image3","image3"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
      ("FullIngressClosure.Initialization","FullIngressClosure","stageTape","stageTape"),
      ("FullIngressClosure.Initialization","FullIngressClosure","partial_old","partialOld"),
      ("FullIngressClosure.Initialization","FullIngressClosure","Before","Before"),
      ("FullIngressClosure.Initialization","FullIngressClosure","before_below","beforeBelow"),
      ("FullIngressClosure.Initialization","FullIngressClosure","delimiter_mono","delimiterMono"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena","Arena"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.mk","arenaMk"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.positive","arenaPositive"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.gap","arenaGap"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.blank","arenaBlank"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.fence","arenaFence"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.marks","arenaMarks"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.space","arenaSpace"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor","Corridor"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.mk","corridorMk"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.order","corridorOrder"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.eof","corridorEof"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.sep","corridorSep"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.endBlank","corridorBlank"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.register","corridorRegister"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.assignment","corridorAssignment") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique original-tape exterior proof {mod}/{key}: {found.map Prod.fst}"
private theorem counter_original (T : Nat → Option Bool) (F r n g ell W i : Nat)
    (outside : i ≤ SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i) :
    counterTape T F r n g ell W i=T i := by
  have avoid (j : Nat) (hj : j < 12) : ¬(SerializedBody.delimiter F r n j < i ∧ i < SerializedBody.delimiter F r n (j+1)) := by
    rcases outside with low | high
    · have h:=delimiterMono F r n 0 j (by omega) (by omega); omega
    · have h:=delimiterMono F r n (j+1) 12 (by omega) le_rfl; omega
  dsimp only [counterTape,halfPhase,image3,arithmeticTape,setBank]
  simp only [if_neg (avoid 1 (by decide)),if_neg (avoid 2 (by decide)),if_neg (avoid 3 (by decide)),
    if_neg (avoid 4 (by decide)),if_neg (avoid 5 (by decide)),if_neg (avoid 6 (by decide)),
    if_neg (avoid 7 (by decide)),if_neg (avoid 8 (by decide)),if_neg (avoid 9 (by decide)),
    if_neg (avoid 10 (by decide)),if_neg (avoid 11 (by decide))]
  rcases outside with low | high
  · exact partialOld (by decide) le_rfl (low.trans (delimiterMono F r n 0 6 (by decide) (by decide)))
  · have fresh : ¬Before F r n 12 i:=by intro h; have bound:=beforeBelow le_rfl h; omega
    dsimp only [stageTape]
    rw [if_neg (by omega),if_neg fresh]
private theorem corridor_congr {T U : Nat → Option Bool} {S L H : Nat} (frame : Corridor T S L H)
    (same : ∀ i,i ≤ H → U i=T i) : Corridor U S L H := by
  have order:=corridorOrder frame
  refine corridorMk order ?_ ?_ ?_ ?_ ?_
  · rw [same S (by omega)]; exact corridorEof frame
  · rw [same L (by omega)]; exact corridorSep frame
  · rw [same H le_rfl]; exact corridorBlank frame
  · intro i il iu; rw [same i (by omega)]; exact corridorRegister frame i il iu
  · intro i il iu; rw [same i (by omega)]; exact corridorAssignment frame i il iu
private theorem arena_congr {T U : Nat → Option Bool} {H F Q : Nat} (frame : Arena T H F Q)
    (same : ∀ i,i ≤ F → U i=T i) : Arena U H F Q := by
  have gap:=arenaGap frame
  have pos:=arenaPositive frame
  refine arenaMk pos gap ?_ ?_ ?_ ?_
  · rw [same H (by omega)]; exact arenaBlank frame
  · rw [same F le_rfl]; exact arenaFence frame
  · intro i il iu; rw [same i (by omega)]; exact arenaMarks frame i il iu
  · intro i il iu; rw [same i (by omega)]; exact arenaSpace frame i il iu
private theorem counter_corridor {S L H F Q} (T : Nat → Option Bool) (r n g ell W : Nat)
    (corridor : Corridor T S L H) (arena : Arena T H F Q) :
    Corridor (counterTape T F r n g ell W) S L H := by
  have gap:=arenaGap arena
  apply corridor_congr corridor
  intro i hi
  exact counter_original T F r n g ell W i (Or.inl (by change i ≤ F+1; omega))
private theorem counter_arena {H F Q} (T : Nat → Option Bool) (r n g ell W : Nat)
    (arena : Arena T H F Q) : Arena (counterTape T F r n g ell W) H F Q := by
  apply arena_congr arena
  intro i hi
  exact counter_original T F r n g ell W i (Or.inl (by change i ≤ F+1; omega))
private theorem counter_source {S L H F Q p} (T : Nat → Option Bool) (r n g ell W : Nat)
    (source : Fin S → Bool) (corridor : Corridor T S L H) (arena : Arena T H F Q)
    (cells : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    ∀ i,p ≤ i → ∀ hi : i < S,counterTape T F r n g ell W i=some (source ⟨i,hi⟩) := by
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  intro i il iu
  rw [counter_original T F r n g ell W i (Or.inl (by change i ≤ F+1; omega))]
  exact cells i il iu
end FullIngressClosure
