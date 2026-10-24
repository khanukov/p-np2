import FullIngressClosure.SourceScan
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","put","put"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mk","gridMk"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.rise","gridRise"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.cells","gridCells"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary"),
      ("FullIngressClosure.Workspace","FullIngressClosure","setBank","setBank"),
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
    | _ => throwError "Nonunique moving-source-hole term {mod}/{key}: {found.map Prod.fst}"
private def lifted (T : Nat → Option Bool) (S q : Nat) : Nat → Option Bool :=
  if q < S then put T q none else T
private theorem put_old {T : Nat → Option Bool} {q i : Nat} (b : Option Bool) (ne : i ≠ q) :
    put T q b i=T i := by dsimp only [put]; rw [if_neg ne]
private theorem put_here (T : Nat → Option Bool) (q : Nat) (b : Option Bool) : put T q b q=b := by
  dsimp only [put]; rw [if_pos rfl]
private theorem put_back (T : Nat → Option Bool) (q : Nat) (b : Option Bool) :
    put (put T q none) q b=put T q b := by
  funext i
  by_cases eq : i=q
  · subst i; rw [put_here,put_here]
  · rw [put_old b eq,put_old none eq,put_old b eq]
private theorem put_current (T : Nat → Option Bool) (q : Nat) : put T q (T q)=T := by
  funext i
  by_cases eq : i=q
  · subst i; exact put_here T q (T q)
  · exact put_old _ eq
private theorem lifted_old {T : Nat → Option Bool} {S q i : Nat} (ne : i ≠ q) : lifted T S q i=T i := by
  dsimp only [lifted]
  split_ifs
  · exact put_old none ne
  · rfl
private theorem lifted_here {T : Nat → Option Bool} {S q : Nat} (qs : q ≤ S) (eof : T S=none) :
    lifted T S q q=none := by
  dsimp only [lifted]
  split_ifs with physical
  · exact put_here T q none
  · have eq : q=S:=by omega
    rwa [eq]
private theorem restore_lifted {T : Nat → Option Bool} {S q : Nat} :
    put (lifted T S q) q (T q)=T := by
  dsimp only [lifted]
  split_ifs
  · rw [put_back,put_current]
  · exact put_current T q
private theorem lifted_virtual (T : Nat → Option Bool) (S q : Nat) (past : S ≤ q) : lifted T S q=T := by
  dsimp only [lifted]; rw [if_neg (by omega)]
private theorem low_put_grid {D T q} (grid : Grid D T) (below : q < D 0) (b : Option Bool) :
    Grid D (put T q b) := by
  refine gridMk (gridRise grid) (gridMono grid) ?_ ?_
  · intro j hj
    have low:=gridMono grid 0 j (by omega) hj
    rw [put_old b (by omega)]
    exact gridBlank grid j hj
  · intro j i hj il iu
    have low:=gridMono grid 0 j (by omega) (by omega)
    rw [put_old b (by omega)]
    exact gridCells grid j i hj il iu
private theorem low_put_unary {D T q j v} (grid : Grid D T) (below : q < D 0) (b : Option Bool)
    (hj : j < 12) (unary : BankUnary D T j v) : BankUnary D (put T q b) j v := by
  intro i il iu
  have low:=gridMono grid 0 j (by omega) (by omega)
  rw [put_old b (by omega)]
  exact unary i il iu
private theorem lifted_grid {D T S q} (grid : Grid D T) (below : S < D 0) (_qs : q ≤ S) :
    Grid D (lifted T S q) := by
  dsimp only [lifted]
  split_ifs
  · exact low_put_grid grid (by omega) none
  · exact grid
private theorem lifted_unary {D T S q j v} (grid : Grid D T) (below : S < D 0) (_qs : q ≤ S)
    (hj : j < 12) (unary : BankUnary D T j v) : BankUnary D (lifted T S q) j v := by
  dsimp only [lifted]
  split_ifs
  · exact low_put_unary grid (by omega) none hj unary
  · exact unary
private theorem bank_below {D T j v i} (grid : Grid D T) (hj : j < 12) (below : i ≤ D 0) :
    setBank T D j v i=T i := by
  have low:=gridMono grid 0 j (by omega) (by omega)
  dsimp only [setBank]
  rw [if_neg (by omega)]
private theorem bank_put {D T q j v} (grid : Grid D T) (below : q < D 0) (hj : j < 12) (b : Option Bool) :
    setBank (put T q b) D j v=put (setBank T D j v) q b := by
  funext i
  by_cases eq : i=q
  · subst i
    rw [put_here]
    dsimp only [setBank]
    have low:=gridMono grid 0 j (by omega) (by omega)
    rw [if_neg (by omega),put_here]
  · dsimp only [setBank,put]
    rw [if_neg eq]
    split_ifs <;> rfl
private theorem bank_lifted {D T S q j v} (grid : Grid D T) (below : S < D 0) (_qs : q ≤ S) (hj : j < 12) :
    setBank (lifted T S q) D j v=lifted (setBank T D j v) S q := by
  dsimp only [lifted]
  split_ifs
  · exact bank_put grid (by omega) hj none
  · rfl
private theorem lifted_corridor {T S L H q} (frame : Corridor T S L H) (qs : q ≤ S) :
    Corridor (lifted T S q) S L H := by
  have order:=corridorOrder frame
  refine corridorMk order ?_ ?_ ?_ ?_ ?_
  · by_cases eq : q=S
    · subst q; rw [lifted_virtual T S S le_rfl]; exact corridorEof frame
    · rw [lifted_old (by omega)]; exact corridorEof frame
  · rw [lifted_old (by omega)]; exact corridorSep frame
  · rw [lifted_old (by omega)]; exact corridorBlank frame
  · intro i il iu
    rw [lifted_old (by omega)]; exact corridorRegister frame i il iu
  · intro i il iu
    rw [lifted_old (by omega)]; exact corridorAssignment frame i il iu
private theorem lifted_arena {T S H F Q q} (frame : Arena T H F Q) (sh : S < H) (qs : q ≤ S) :
    Arena (lifted T S q) H F Q := by
  have hQ:=arenaPositive frame
  have gap:=arenaGap frame
  refine arenaMk hQ gap ?_ ?_ ?_ ?_
  · rw [lifted_old (by omega)]; exact arenaBlank frame
  · rw [lifted_old (by omega)]; exact arenaFence frame
  · intro i il iu
    rw [lifted_old (by omega)]; exact arenaMarks frame i il iu
  · intro i il iu
    rw [lifted_old (by omega)]; exact arenaSpace frame i il iu
private theorem bank_corridor {D T S L H j v} (grid : Grid D T) (frame : Corridor T S L H)
    (hj : j < 12) (below : H ≤ D 0) : Corridor (setBank T D j v) S L H := by
  have order:=corridorOrder frame
  refine corridorMk order ?_ ?_ ?_ ?_ ?_
  · rw [bank_below grid hj (by omega)]; exact corridorEof frame
  · rw [bank_below grid hj (by omega)]; exact corridorSep frame
  · rw [bank_below grid hj below]; exact corridorBlank frame
  · intro i il iu
    rw [bank_below grid hj (by omega)]; exact corridorRegister frame i il iu
  · intro i il iu
    rw [bank_below grid hj (by omega)]; exact corridorAssignment frame i il iu
private theorem bank_arena {D T H F Q j v} (grid : Grid D T) (frame : Arena T H F Q)
    (hj : j < 12) (d0 : D 0=F+1) : Arena (setBank T D j v) H F Q := by
  have hQ:=arenaPositive frame
  have gap:=arenaGap frame
  refine arenaMk hQ gap ?_ ?_ ?_ ?_
  · rw [bank_below grid hj (by omega)]; exact arenaBlank frame
  · rw [bank_below grid hj (by omega)]; exact arenaFence frame
  · intro i il iu
    rw [bank_below grid hj (by omega)]; exact arenaMarks frame i il iu
  · intro i il iu
    rw [bank_below grid hj (by omega)]; exact arenaSpace frame i il iu
private theorem lifted_source {T : Nat → Option Bool} {S q i : Nat}
    (source : T i=some true ∨ T i=some false) (different : q < i) :
    lifted T S q i=some true ∨ lifted T S q i=some false := by
  rw [lifted_old (by omega)]
  exact source
end FullIngressClosure
