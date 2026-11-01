import FullBodyClosure.Fold
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
open Lean Elab Tactic in
private def checkedFrom (owner : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong owner: {name}"
  logInfo m!"invariant-adapter|{name}|{ci.type}"
  closeMainGoal `checkedFrom (mkConst name (ci.levelParams.map Level.param))
open Lean Elab Tactic in
private def checkedKernel (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num `_private.SerializedBodyCompletion.Kernel 0) "SerializedBodyCompletion")
  let some ci:=env.find? name | throwError "Missing exact kernel declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing kernel owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == `SerializedBodyCompletion.Kernel do throwError "Wrong kernel owner: {name}"
  logInfo m!"operand-adapter|{name}|{ci.type}"
  closeMainGoal `checkedKernel (mkConst name (ci.levelParams.map Level.param))
private abbrev Node : Type := by run_tac checkedKernel "Node"
private abbrev node : Fin 7500 → Nat → (Nat → Option Bool) → Node := by run_tac checkedKernel "Node.mk"
private abbrev nodeHead : Node → Nat := by run_tac checkedKernel "Node.head"
private abbrev Path : Nat → Nat → Node → Node → Prop := by run_tac checkedKernel "Path"
private abbrev Grid : (Nat → Nat) → (Nat → Option Bool) → Prop := by run_tac checkedKernel "Grid"
private abbrev Unary : (Nat → Nat) → (Nat → Option Bool) → Nat → Nat → Prop := by run_tac checkedKernel "Unary"
private abbrev embed : ∀ {N B : Nat} (c : Node),nodeHead c < tapeLength N B → Config 7500 N B := by run_tac checkedKernel "embed"
private theorem Path.bounds : ∀ {P t a b},Path P t a b → nodeHead a   ≤   P ∧ nodeHead b   ≤   P := by run_tac checkedKernel "Path.bounds"
private theorem Path.append : ∀ {P t u a b c},Path P t a b → Path P u b c → Path P (t+u) a c := by run_tac checkedKernel "Path.append"
private theorem Path.execute : ∀ {N B P t a b} (h : Path P t a b) (fit : P < tapeLength N B),
  SerializedBody.machine.run t (embed a (lt_of_le_of_lt h.bounds.1 fit))=embed b (lt_of_le_of_lt h.bounds.2 fit) := by run_tac checkedKernel "Path.execute"
private theorem Path.prefix : ∀ {P t a b} (h : Path P t a b) {N B : Nat} (fit : P < tapeLength N B),
  ∀ u,u < t → 4   ≤   (SerializedBody.machine.run u (embed a (lt_of_le_of_lt h.bounds.1 fit))).state.val := by run_tac checkedKernel "Path.prefix"
private abbrev Context : (Nat → Nat) → (Nat → Option Bool) → (S L H Q F r M W n : Nat) →
    (Fin S → Bool) → (Fin n → Bool) → Prop := by run_tac checkedFrom `FullBodyClosure.Invariant "Context"
private abbrev memory : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Representation "memory"
private abbrev counter : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Index "counter"
private abbrev place : (Nat → Option Bool) → Nat → List Bool → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.BufferModel "place"
private abbrev put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by run_tac checkedKernel "put"
private theorem grid_mono : ∀ {D T},Grid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by run_tac checkedKernel "Grid.mono"
private theorem grid_rise : ∀ {D T},Grid D T → ∀ j,j < 12 → D j < D (j+1) := by run_tac checkedKernel "Grid.rise"
private theorem grid_blank : ∀ {D T},Grid D T → ∀ j,j ≤ 12 → T (D j)=none := by run_tac checkedKernel "Grid.blank"
private theorem grid_cells : ∀ {D T},Grid D T → ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b := by run_tac checkedKernel "Grid.cells"
private theorem Context.grid : ∀ {D T S L H Q F r M W n source beta},Context D T S L H Q F r M W n source beta → Grid D T := by run_tac checkedFrom `FullBodyClosure.Invariant "Context.grid"
private theorem Context.before : ∀ {D T S L H Q F r M W n source beta},Context D T S L H Q F r M W n source beta → S < D 0 := by run_tac checkedFrom `FullBodyClosure.Invariant "Context.before"
private theorem Context.withCounter : ∀ {D T S L H Q F r M W n source beta},Context D T S L H Q F r M W n source beta →
    ∀ j v,j < 12 → Context D (counter T D j v) S L H Q F r M W n source beta := by run_tac checkedFrom `FullBodyClosure.Invariant "Context.withCounter"
private theorem Context.withWorkspace : ∀ {D T S L H Q F r M W n source beta},Context D T S L H Q F r M W n source beta →
    ∀ U,(∀ i,i < D 0 → U i=T i) → (∀ j,j ≤ 12 → U (D j)=none) →
      (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,U i=some b) →
      Context D U S L H Q F r M W n source beta := by run_tac checkedFrom `FullBodyClosure.Invariant "Context.withWorkspace"
private theorem place_grid : ∀ {D T},Grid D T → ∀ a bits,D 9 < a → a+2*bits.length ≤ D 10 → Grid D (place T a bits) := by run_tac checkedFrom `FullBodyClosure.Fold "place_grid"
private theorem place_below : ∀ {D T},Grid D T → ∀ bits i,i < D 0 → place T (D 9+1) bits i=T i := by run_tac checkedFrom `FullBodyClosure.Fold "place_below"
private theorem place_outside : ∀ T a bits i,i<a ∨ a+2*bits.length ≤ i → place T a bits i=T i := by run_tac checkedFrom `FullBodyClosure.Fold "place_outside"
private theorem memory_below : ∀ {T D S M W u i},(∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) → i < D 0 →
    memory T D S M W u i=(if i=M+u ∧ i < S then none else T i) := by run_tac checkedFrom `FullBodyClosure.Representation "memory_below"
private theorem memory_patch : ∀ (T : Nat → Option Bool) (D : Nat → Nat) (S M W u h : Nat) (b : Option Bool),
    S ≤ h → ¬(D 4 < h ∧ h < D 5) → ¬(D 11 < h ∧ h < D 12) →
    put (memory T D S M W u) h b=memory (put T h b) D S M W u := by run_tac checkedFrom `FullBodyClosure.Representation "memory_patch"
private theorem read_plain {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u N B P : Nat) (site : Fin 9)
    (hu : u < W) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 64*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getEntry site (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyRefinement.getExit site (padRead source (M+u)) (SerializedBody.sourceMode source (M+(u+1))),⟨D 0,h0⟩,
        fun i=>memory T D S M W (u+1) i.val⟩ : Config 7500 N B) := by
  rcases ctx with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
  obtain ⟨_bit,t,price,run,before⟩:=SerializedPositiveBody.positive_reader site D T S L H Q F r M W u N B P source
    hu hw sl lh positive arena anchor rise mono blank cells len4 len11 eof left right fence reg ass marks gap src room fit h0
  exact ⟨t,price,run,by intro j hj;exact before j (by omega)⟩
private theorem memory_grid {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u : Nat) : Grid D (memory T D S M W u) := by
  have before:=ctx.before
  have grid:=ctx.grid
  rcases ctx with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
  constructor
  · exact rise
  · exact mono
  · intro j hj
    have order:=mono 0 j (by omega) hj
    have notField (k : Nat) (hk : k < 12) : ¬(D k < D j ∧ D j < D (k+1)) := by
      by_cases atLeft : j ≤ k
      · have :=mono j k atLeft (by omega);omega
      · have :=mono (k+1) j (by omega) hj;omega
    change (if D j=M+u ∧ D j < S then none else if D 4 < D j ∧ D j < D 5 then _ else
      if D 11 < D j ∧ D j < D 12 then _ else T (D j))=none
    rw [if_neg (by omega : ¬(D j=M+u ∧ D j < S)),if_neg (notField 4 (by decide)),if_neg (notField 11 (by decide)),blank j hj]
  · intro j i hj lo hi
    have order:=mono 0 j (by omega) (by omega)
    change ∃ b,(if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else if D 11 < i ∧ i < D 12 then _ else T i)=some b
    rw [if_neg (by omega : ¬(i=M+u ∧ i < S))]
    split_ifs with a b
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact cells j i hj lo hi
private theorem Context.withBuffer {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (bits : List Bool)
    (room : D 9+1+2*bits.length ≤ D 10) : Context D (place T (D 9+1) bits) S L H Q F r M W n source beta := by
  have grid:=place_grid ctx.grid (D 9+1) bits (by omega) room
  exact ctx.withWorkspace _ (place_below ctx.grid bits) (grid_blank grid) (grid_cells grid)
private theorem memory_place {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (a u : Nat) (bits : List Bool)
    (lo : D 9 < a) (hi : a+2*bits.length ≤ D 10) :
    place (memory T D S M W u) a bits=memory (place T a bits) D S M W u := by
  have before:=ctx.before
  have mono:=grid_mono ctx.grid
  induction bits generalizing T a with
  | nil => rfl
  | cons b bs ih =>
    have ord1:=mono 5 9 (by decide) (by decide)
    have ord2:=mono 10 11 (by decide) (by decide)
    have room : a+1 < D 10 := by simp only [List.length_cons] at hi;omega
    have p0:=memory_patch T D S M W u a (some true) (by have :=mono 0 9 (by decide) (by decide);omega)
      (by omega) (by omega)
    have p1:=memory_patch (put T a (some true)) D S M W u (a+1) (some b)
      (by have :=mono 0 9 (by decide) (by decide);omega) (by omega) (by omega)
    change place (put (put (memory T D S M W u) a (some true)) (a+1) (some b)) (a+2) bs=_
    rw [p0,p1]
    have g0:=grid_cells ctx.grid 9 a (by decide) lo (by change a<D 10;omega)
    have g1:=grid_cells ctx.grid 9 (a+1) (by decide) (by omega) room
    have ctx' : Context D (put (put T a (some true)) (a+1) (some b)) S L H Q F r M W n source beta := by
      apply ctx.withWorkspace
      · intro i low
        have left:=mono 0 9 (by decide) (by decide)
        change (if i=a+1 then some b else if i=a then some true else T i)=T i
        rw [if_neg (by omega : i≠a+1),if_neg (by omega : i≠a)]
      · intro j hj
        have atSep : D j≠a ∧ D j≠a+1 := by
          by_cases le : j ≤ 9
          · have :=mono j 9 le (by decide);omega
          · have :=mono 10 j (by omega) hj;omega
        change (if D j=a+1 then some b else if D j=a then some true else T (D j))=none
        rw [if_neg atSep.2,if_neg atSep.1,grid_blank ctx.grid j hj]
      · intro j i hj lower upper
        change ∃ c,(if i=a+1 then some b else if i=a then some true else T i)=some c
        split_ifs with e f
        · exact ⟨_,rfl⟩
        · exact ⟨_,rfl⟩
        · exact grid_cells ctx.grid j i hj lower upper
    exact ih ctx' (a+2) (by omega) (by simp only [List.length_cons] at hi;omega)
private theorem memory_counter {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u j v : Nat)
    (hj : j < 12) (ne4 : j≠4) (ne11 : j≠11) :
    counter (memory T D S M W u) D j v=memory (counter T D j v) D S M W u := by
  have before:=ctx.before
  have mono:=grid_mono ctx.grid
  funext i
  by_cases inside : D j < i ∧ i < D (j+1)
  · have low:=mono 0 j (by omega) (by omega)
    have apart (k : Nat) (hk : k < 12) (ne : j≠k) : ¬(D k < i ∧ i < D (k+1)) := by
      by_cases le : j < k
      · have :=mono (j+1) k (by omega) (by omega);omega
      · have :=mono (k+1) j (by omega) (by omega);omega
    change (if D j < i ∧ i < D (j+1) then _ else _)=(if i=M+u ∧ i < S then none else
      if D 4 < i ∧ i < D 5 then _ else if D 11 < i ∧ i < D 12 then _ else
        if D j < i ∧ i < D (j+1) then _ else _)
    simp only [if_pos inside,if_neg (show ¬(i=M+u ∧ i < S) from by omega),
      if_neg (apart 4 (by decide) ne4),if_neg (apart 11 (by decide) ne11)]
  · change (if D j < i ∧ i < D (j+1) then _ else _)=(if i=M+u ∧ i < S then none else
      if D 4 < i ∧ i < D 5 then _ else if D 11 < i ∧ i < D 12 then _ else
        if D j < i ∧ i < D (j+1) then _ else _)
    simp only [if_neg inside]
    rfl
private theorem memory_unary {D T S L H Q F r M W n source beta j v}
    (ctx : Context D T S L H Q F r M W n source beta) (u : Nat)
    (hj : j < 12) (ne4 : j≠4) (ne11 : j≠11) (unary : Unary D T j v) :
    Unary D (memory T D S M W u) j v := by
  have eq:=memory_counter ctx u j v hj ne4 ne11
  have fixed : counter T D j v=T := by
    funext i
    change (if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else T i)=T i
    split_ifs with h
    · exact (unary i h.1 h.2).symm
    · rfl
  rw [fixed] at eq
  intro i lo hi
  have atCell:=congrFun eq i
  change (if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else _)=_ at atCell
  rw [if_pos ⟨lo,hi⟩] at atCell
  exact atCell.symm
private abbrev DecRows : Nat → Fin 7500 → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "DecRows"
private theorem keep : ∀ {P : Nat} (s q : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (mv : Move),
    h ≤ P → h' ≤ P → 4 ≤ s.val → SerializedBody.machine.step s (T h)=(q,T h,mv) →
    (match mv with | .left=>h-1 | .stay=>h | .right=>h+1)=h' →
    Path P 1 (node s h T) (node q h' T) := by run_tac checkedKernel "keep"
private theorem dec_zero : ∀ {D T j w P start zero pos},Grid D T → j < 12 → D 12 ≤ P →
    D (j+1)=D j+w+1 → Unary D T j 0 → DecRows j start zero pos →
    Path P (2*(D j-D 0+j)+3) (node start (D 0) T) (node zero (D 0) T) := by run_tac checkedKernel "dec_zero"
private theorem dec_positive : ∀ {D T j w v P start zero pos},Grid D T → j < 12 → D 12 ≤ P →
    D (j+1)=D j+w+1 → Unary D T j v → 0 < v → v ≤ w → DecRows j start zero pos →
    Path P (2*(D j-D 0+j)+2*v+4) (node start (D 0) T)
      (node pos (D 0) (put T (D j+v) (some false))) := by run_tac checkedKernel "dec_positive"
private theorem counter_unary : ∀ T D j v,Unary D (counter T D j v) j v := by run_tac checkedFrom `FullBodyClosure.Index "counter_unary"
private theorem counter_down : ∀ T D j v w,D (j+1)=D j+w+1 → 0 < v → v ≤ w →
    put (counter T D j v) (D j+v) (some false)=counter T D j (v-1) := by run_tac checkedFrom `FullBodyClosure.Index "counter_down"
private theorem path_native {N B P t a b} (path : Path P t a b) (fit : P < tapeLength N B) :
    Native t (embed a (lt_of_le_of_lt path.bounds.1 fit)) (embed b (lt_of_le_of_lt path.bounds.2 fit)) :=
  ⟨path.execute fit,path.prefix fit⟩
private abbrev foldState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "foldState"
private abbrev readState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Invariant "readIndexState"
private theorem read_actual (m : Fin 3) : ∃ d : Fin 7500,4 ≤ (readState m).val ∧
    SerializedBody.machine.step (readState m) none=(d,none,.stay) ∧
    DecRows 8 d (foldState m) (SerializedBodyRefinement.getEntry ⟨8,by decide⟩ m) := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.InputRows0 "readIndexCode0"
  · run_tac checkedFrom `FullBodyClosure.InputRows1 "readIndexCode1"
  · run_tac checkedFrom `FullBodyClosure.InputRows2 "readIndexCode2"
private theorem index_down {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u j N B P : Nat) (m : Fin 3)
    (len8 : D 9=D 8+n+1) (small : j ≤ n) (positive : 0 < j)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 64*(P+1) ∧ Native t
      (⟨readState m,⟨D 0,h0⟩,fun i=>memory (counter T D 8 j) D S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyRefinement.getEntry ⟨8,by decide⟩ m,⟨D 0,h0⟩,
        fun i=>memory (counter T D 8 (j-1)) D S M W u i.val⟩ : Config 7500 N B) := by
  let U:=memory (counter T D 8 j) D S M W u
  have grid:=memory_grid (ctx.withCounter 8 j (by decide)) u
  obtain ⟨d,safe,jump,code⟩:=read_actual m
  have root:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
  have one:=keep (readState m) d (D 0) (D 0) U .stay (P:=P) root root safe
    (by rw [show U (D 0)=none from grid_blank grid 0 (by decide)];exact jump) rfl
  have two:=dec_positive grid (j:=8) (by decide) room len8
    (memory_unary (ctx.withCounter 8 j (by decide)) u (by decide) (by decide) (by decide) (counter_unary T D 8 j))
    positive small code
  have old:=memory_counter ctx u 8 j (by decide) (by decide) (by decide)
  have after:=counter_down (memory T D S M W u) D 8 j n len8 positive small
  rw [old,memory_counter ctx u 8 (j-1) (by decide) (by decide) (by decide)] at after
  rw [after] at two
  have path:=one.append two
  refine ⟨_,?_,path_native path fit⟩
  have width:=grid_mono grid 9 12 (by decide) (by decide)
  omega
private theorem index_zero {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u N B P : Nat) (m : Fin 3)
    (len8 : D 9=D 8+n+1) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 64*(P+1) ∧ Native t
      (⟨readState m,⟨D 0,h0⟩,fun i=>memory (counter T D 8 0) D S M W u i.val⟩ : Config 7500 N B)
      (⟨foldState m,⟨D 0,h0⟩,fun i=>memory (counter T D 8 0) D S M W u i.val⟩ : Config 7500 N B) := by
  let U:=memory (counter T D 8 0) D S M W u
  have grid:=memory_grid (ctx.withCounter 8 0 (by decide)) u
  obtain ⟨d,safe,jump,code⟩:=read_actual m
  have root:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
  have one:=keep (readState m) d (D 0) (D 0) U .stay (P:=P) root root safe
    (by rw [show U (D 0)=none from grid_blank grid 0 (by decide)];exact jump) rfl
  have two:=dec_zero grid (j:=8) (by decide) room len8
    (memory_unary (ctx.withCounter 8 0 (by decide)) u (by decide) (by decide) (by decide) (counter_unary T D 8 0)) code
  have path:=one.append two
  refine ⟨_,?_,path_native path fit⟩
  have width:=grid_mono grid 8 12 (by decide) (by decide)
  omega

private theorem place_counter : ∀ {D : Nat → Nat} (j v : Nat) (bits : List Bool) (T : Nat → Option Bool)
    (a : Nat),D (j+1) ≤ a → place (counter T D j v) a bits=counter (place T a bits) D j v := by
  run_tac checkedFrom `FullBodyClosure.Fold "place_counter"
private theorem place_pair : ∀ T a bits j,(hj : j < bits.length) →
    place T a bits (a+2*j)=some true ∧ place T a bits (a+2*j+1)=some (bits[j]'hj) := by
  run_tac checkedFrom `FullBodyClosure.Fold "place_pair"
private theorem place_snoc : ∀ T a bits b,place T a (bits++[b])=
    put (put (place T a bits) (a+2*bits.length) (some true)) (a+2*bits.length+1) (some b) := by
  run_tac checkedFrom `FullBodyClosure.BufferModel "place_snoc"
private abbrev AppendRows : Fin 7500 → Fin 7500 → Bool → Prop := by run_tac checkedFrom `FullBodyClosure.Buffer "AppendRows"
private theorem append_path : ∀ {D T P d start out} (b : Bool),Grid D T → D 12 ≤ P →
    D 9+2*d+3 ≤ D 10 → (∀ j,j < d → T (D 9+1+2*j)=some true ∧ ∃ b,T (D 9+1+2*j+1)=some b) →
    T (D 9+2*d+1)=some false → (∃ b,T (D 9+2*d+2)=some b) → AppendRows start out b →
    Path P (2*(D 9-D 0)+4*d+24) (node start (D 0) T)
      (node out (D 0) (put (put T (D 9+2*d+1) (some true)) (D 9+2*d+2) (some b))) := by
  run_tac checkedFrom `FullBodyClosure.Buffer "append_path"
private theorem append_actual (m : Fin 3) (b : Bool) :
    AppendRows (SerializedBodyRefinement.getExit ⟨8,by decide⟩ b m) (readState m) b := by
  fin_cases m <;> cases b
  · run_tac checkedFrom `FullBodyClosure.InputRows0 "appendCode0_0"
  · run_tac checkedFrom `FullBodyClosure.InputRows0 "appendCode0_1"
  · run_tac checkedFrom `FullBodyClosure.InputRows1 "appendCode1_0"
  · run_tac checkedFrom `FullBodyClosure.InputRows1 "appendCode1_1"
  · run_tac checkedFrom `FullBodyClosure.InputRows2 "appendCode2_0"
  · run_tac checkedFrom `FullBodyClosure.InputRows2 "appendCode2_1"
private theorem memory_buffer {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u i : Nat)
    (lo : D 9 < i) (hi : i < D 10) : memory T D S M W u i=T i := by
  have before:=ctx.before
  have mono:=grid_mono ctx.grid
  have a:=mono 5 9 (by decide) (by decide)
  have b:=mono 10 11 (by decide) (by decide)
  have c:=mono 0 9 (by decide) (by decide)
  change (if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else
    if D 11 < i ∧ i < D 12 then _ else T i)=T i
  rw [if_neg (by omega : ¬(i=M+u ∧ i < S)),if_neg (by omega : ¬(D 4 < i ∧ i < D 5)),
    if_neg (by omega : ¬(D 11 < i ∧ i < D 12))]
private theorem append_digit {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u j N B P : Nat) (m : Fin 3) (b : Bool)
    (len9 : D 10=D 9+2*r+1) (bits : List Bool) (small : bits.length < r)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 64*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getExit ⟨8,by decide⟩ b m,⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) bits) D 8 j) D S M W u i.val⟩ : Config 7500 N B)
      (⟨readState m,⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) (bits++[b])) D 8 j) D S M W u i.val⟩ : Config 7500 N B) := by
  let U:=memory (counter T D 8 j) D S M W u
  have ctx':=ctx.withCounter 8 j (by decide)
  have grid:=memory_grid ctx' u
  have freeU (i : Nat) (lo : D 9 < i) (hi : i < D 10) : U i=some false := by
    change memory (counter T D 8 j) D S M W u i=some false
    rw [memory_buffer ctx' u i lo hi]
    have order:=grid_mono ctx.grid 9 9 (by decide) (by decide)
    change (if D 8 < i ∧ i < D 9 then _ else T i)=some false
    rw [if_neg (by omega : ¬(D 8 < i ∧ i < D 9))];exact free i lo hi
  have gV:=place_grid grid (D 9+1) bits (by omega) (by omega)
  have path:=append_path (d:=bits.length) b gV room (by omega)
    (by intro q hq;exact ⟨(place_pair U _ bits q hq).1,_,(place_pair U _ bits q hq).2⟩)
    (by rw [place_outside U _ bits _ (Or.inr (by omega))];exact freeU _ (by omega) (by omega))
    (by rw [place_outside U _ bits _ (Or.inr (by omega))];exact ⟨false,freeU _ (by omega) (by omega)⟩)
    (append_actual m b)
  have coords0 : D 9+2*bits.length+1=D 9+1+2*bits.length := by omega
  have coords1 : D 9+2*bits.length+2=D 9+1+2*bits.length+1 := by omega
  rw [coords0,coords1,←place_snoc U _ bits b] at path
  have same (bs : List Bool) (bound : bs.length ≤ r) : place U (D 9+1) bs=
      memory (counter (place T (D 9+1) bs) D 8 j) D S M W u := by
    rw [memory_place ctx' (D 9+1) u bs (by omega) (by omega),
      place_counter 8 j bs T _ (by change D 9 ≤ D 9+1;omega)]
  rw [same bits (by omega),same (bits++[b]) (by simp;omega)] at path
  refine ⟨_,?_,path_native path fit⟩
  have upper:=grid_mono ctx.grid 10 12 (by decide) (by decide)
  omega
private theorem window_succ {S : Nat} (source : Fin S → Bool) (M width : Nat) :
    SerializedBody.window source M (width+1)=padRead source M::SerializedBody.window source (M+1) width := by
  simp only [SerializedBody.window,List.ofFn_succ]
  congr 1
  apply congrArg (fun f : Fin width → Bool=>List.ofFn f)
  funext i
  congr 1
  change M+(i.val+1)=M+1+i.val
  omega

private theorem index_read {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (N B P : Nat)
    (len8 : D 9=D 8+n+1) (len9 : D 10=D 9+2*r+1)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∀ j u (bits : List Bool),j ≤ n → bits.length+j ≤ r → u+j ≤ W →
    ∃ t,t ≤ 256*(j+1)*(P+1) ∧ Native t
      (⟨readState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) bits) D 8 j) D S M W u i.val⟩ : Config 7500 N B)
      (⟨foldState (SerializedBody.sourceMode source (M+(u+j))),⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) (bits++SerializedBody.window source (M+u) j)) D 8 0)
          D S M W (u+j) i.val⟩ : Config 7500 N B) := by
  intro j
  induction j with
  | zero =>
    intro u bits _hn len _window
    have ctxB:=ctx.withBuffer bits (by omega)
    obtain ⟨t,price,path⟩:=index_zero ctxB u N B P (SerializedBody.sourceMode source (M+u)) len8 room fit h0
    refine ⟨t,by nlinarith,?_⟩
    simpa only [Nat.add_zero,SerializedBody.window,List.ofFn_zero,List.append_nil] using path
  | succ j ih =>
    intro u bits hn len window
    have ctxB:=ctx.withBuffer bits (by omega)
    obtain ⟨a,pa,down⟩:=index_down ctxB u (j+1) N B P (SerializedBody.sourceMode source (M+u))
      len8 hn (by omega) room fit h0
    simp only [Nat.add_sub_cancel] at down
    obtain ⟨b,pb,read⟩:=read_plain (ctxB.withCounter 8 j (by decide)) u N B P ⟨8,by decide⟩
      (by omega) room fit h0
    obtain ⟨c,pc,append⟩:=append_digit ctx (u+1) j N B P (SerializedBody.sourceMode source (M+(u+1)))
      (padRead source (M+u)) len9 bits (by omega) free room fit h0
    obtain ⟨d,pd,tail⟩:=ih (u+1) (bits++[padRead source (M+u)]) (by omega) (by simp;omega) (by omega)
    have path:=native_trans (native_trans (native_trans down read) append) tail
    refine ⟨a+b+c+d,?_,?_⟩
    · nlinarith
    · have offset : u+1+j=u+(j+1) := by omega
      have shift : M+(u+1)=M+u+1 := by omega
      simpa only [offset,shift,List.append_assoc,window_succ,List.cons_append,List.nil_append] using path

private theorem consume_digits {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (N B P : Nat)
    (len8 : D 9=D 8+n+1) (len9 : D 10=D 9+2*r+1)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∀ count j u (bits : List Bool),count ≤ j → j ≤ n → bits.length+j ≤ r → u+count ≤ W →
    ∃ t,t ≤ 192*count*(P+1) ∧ Native t
      (⟨readState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) bits) D 8 j) D S M W u i.val⟩ : Config 7500 N B)
      (⟨readState (SerializedBody.sourceMode source (M+(u+count))),⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) (bits++SerializedBody.window source (M+u) count)) D 8 (j-count))
          D S M W (u+count) i.val⟩ : Config 7500 N B) := by
  intro count
  induction count with
  | zero =>
    intro j u bits _count _hn _len _window
    refine ⟨0,by omega,?_⟩
    simp only [Nat.add_zero,Nat.sub_zero,SerializedBody.window,List.ofFn_zero,List.append_nil]
    exact ⟨rfl,by intro v hv;omega⟩
  | succ count ih =>
    intro j u bits countBound hn len window
    have ctxB:=ctx.withBuffer bits (by omega)
    obtain ⟨a,pa,down⟩:=index_down ctxB u j N B P (SerializedBody.sourceMode source (M+u))
      len8 hn (by omega) room fit h0
    obtain ⟨b,pb,read⟩:=read_plain (ctxB.withCounter 8 (j-1) (by decide)) u N B P ⟨8,by decide⟩
      (by omega) room fit h0
    obtain ⟨c,pc,append⟩:=append_digit ctx (u+1) (j-1) N B P (SerializedBody.sourceMode source (M+(u+1)))
      (padRead source (M+u)) len9 bits (by omega) free room fit h0
    obtain ⟨d,pd,tail⟩:=ih (j-1) (u+1) (bits++[padRead source (M+u)]) (by omega) (by omega)
      (by simp;omega) (by omega)
    have path:=native_trans (native_trans (native_trans down read) append) tail
    refine ⟨a+b+c+d,?_,?_⟩
    · nlinarith
    · have offset : u+1+count=u+(count+1) := by omega
      have shift : M+(u+1)=M+u+1 := by omega
      have quota : j-1-count=j-(count+1) := by omega
      simpa only [offset,shift,quota,List.append_assoc,window_succ,List.cons_append,List.nil_append] using path
private theorem empty_get {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (N B P : Nat) (site : Fin 9) (m : Fin 3)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 64*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getEntry site m,⟨D 0,h0⟩,fun i=>memory T D S M W W i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyRefinement.getAbort m,⟨D 0,h0⟩,fun i=>memory T D S M W W i.val⟩ : Config 7500 N B) := by
  have grid:=memory_grid ctx W
  have before:=ctx.before
  rcases ctx with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
  have mono0:=mono 0 4 (by decide) (by decide)
  have mono11:=mono 5 11 (by decide) (by decide)
  obtain ⟨run,prefixBound⟩:=SerializedBodyRefinement.counter_phase site m D (memory T D S M W W)
    r 0 W N B P (by omega) rise mono (grid_blank grid) (grid_cells grid) len4 len11
    (by
      intro i lo hi
      change (if i=M+W ∧ i < S then none else if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-W)) else _)=_
      rw [if_neg (by omega : ¬(i=M+W ∧ i < S)),if_pos ⟨lo,hi⟩,Nat.sub_self])
    (by
      intro i lo hi
      have before11:=mono 0 11 (by decide) (by decide)
      change (if i=M+W ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else
        if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ W)) else _)=_
      rw [if_neg (by omega : ¬(i=M+W ∧ i < S)),if_neg (by omega : ¬(D 4 < i ∧ i < D 5)),if_pos ⟨lo,hi⟩])
    room fit h0
  refine ⟨2*(D 4-D 0+4)+3,?_,run,?_⟩
  · have :=mono 4 12 (by decide) (by decide);omega
  · intro v hv
    apply prefixBound v
    change v ≤ 2*(D 4-D 0+4)+3
    omega

/-- Every index digit read is a priced physical consumer. Logical exhaustion
reaches the actual live abort only after its final J-decrement and Get counter phase. -/
private theorem index_read_total {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (N B P : Nat)
    (len8 : D 9=D 8+n+1) (len9 : D 10=D 9+2*r+1)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B)
    (j u : Nat) (bits : List Bool) (hn : j ≤ n) (capacity : bits.length+j ≤ r) (cursor : u ≤ W) :
    let count:=min j (W-u)
    let payload:=bits++SerializedBody.window source (M+u) count
    ∃ t,t ≤ 256*(j+1)*(P+1) ∧
      if j ≤ W-u then Native t
        (⟨readState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
          fun i=>memory (counter (place T (D 9+1) bits) D 8 j) D S M W u i.val⟩ : Config 7500 N B)
        (⟨foldState (SerializedBody.sourceMode source (M+(u+count))),⟨D 0,h0⟩,
          fun i=>memory (counter (place T (D 9+1) payload) D 8 0) D S M W (u+count) i.val⟩ : Config 7500 N B)
      else Native t
        (⟨readState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
          fun i=>memory (counter (place T (D 9+1) bits) D 8 j) D S M W u i.val⟩ : Config 7500 N B)
        (⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+(u+count))),⟨D 0,h0⟩,
          fun i=>memory (counter (place T (D 9+1) payload) D 8 (j-count-1)) D S M W (u+count) i.val⟩ : Config 7500 N B) := by
  dsimp only
  by_cases enough : j ≤ W-u
  · simp only [if_pos enough,min_eq_left enough]
    exact index_read ctx N B P len8 len9 free room fit h0 j u bits hn capacity (by omega)
  · simp only [if_neg enough,min_eq_right (by omega : W-u ≤ j)]
    obtain ⟨t,price,first⟩:=consume_digits ctx N B P len8 len9 free room fit h0 (W-u) j u bits
      (by omega) hn capacity (by omega)
    have finish : u+(W-u)=W := by omega
    rw [finish] at first
    let payload:=bits++SerializedBody.window source (M+u) (W-u)
    have len : payload.length ≤ r := by
      dsimp only [payload]
      simp only [List.length_append,SerializedBody.window,List.length_ofFn]
      omega
    have ctxB:=ctx.withBuffer payload (by omega)
    obtain ⟨s,ps,next⟩:=index_down ctxB W (j-(W-u)) N B P (SerializedBody.sourceMode source (M+W))
      len8 (by omega) (by omega) room fit h0
    obtain ⟨v,pv,last⟩:=empty_get (ctxB.withCounter 8 (j-(W-u)-1) (by decide)) N B P
      ⟨8,by decide⟩ (SerializedBody.sourceMode source (M+W)) room fit h0
    have total:=native_trans (native_trans first next) last
    refine ⟨t+s+v,?_,?_⟩
    · nlinarith
    · simpa only [finish] using total

private abbrev GuardRows : Fin 7500 → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Guard "GuardRows"
private abbrev inputState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Control "inputState"
private abbrev copyState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Invariant "copyState"
private theorem guard_actual (m : Fin 3) : GuardRows (inputState m) (copyState m) (SerializedBodyRefinement.getAbort m) := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.Guard "guardCode0"
  · run_tac checkedFrom `FullBodyClosure.Guard "guardCode1"
  · run_tac checkedFrom `FullBodyClosure.Guard "guardCode2"
private theorem guard_run : ∀ {D T P n start good bad},Grid D T → D 12 ≤ P → D 2=D 1+n+1 →
    GuardRows start good bad → ∃ t,t ≤ 16*(P+1) ∧ Path P t
      (node start (D 0) T) (node (if n=0 then bad else good) (D 0) T) := by run_tac checkedFrom `FullBodyClosure.Guard "guard_run"
private theorem copy_restore : ∀ {D T P n r ell} (m : Fin 3),Grid D T → D 12 ≤ P →
    D 2=D 1+n+1 → D 3=D 2+r+1 → D 9=D 8+n+1 → ell ≤ n → ell ≤ r →
    Unary D T 2 ell → Unary D T 1 0 → Unary D T 8 0 →
    ∃ t,t ≤ 256*(ell+1)*(P+1) ∧ Path P t
      (node (copyState m) (D 0) T) (node (readState m) (D 0) (counter T D 8 ell)) := by
  run_tac checkedFrom `FullBodyClosure.Invariant "copy_restore"
private theorem prepare_index {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u N B P ell : Nat) (m : Fin 3)
    (len1 : D 2=D 1+n+1) (len2 : D 3=D 2+r+1) (len8 : D 9=D 8+n+1)
    (small : ell ≤ n) (bound : ell ≤ r) (u2 : Unary D T 2 ell) (u1 : Unary D T 1 0) (u8 : Unary D T 8 0)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 512*(ell+1)*(P+1) ∧ Native t
      (⟨inputState m,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (if n=0 then ⟨SerializedBodyRefinement.getAbort m,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
       else ⟨readState m,⟨D 0,h0⟩,fun i=>memory (counter T D 8 ell) D S M W u i.val⟩ : Config 7500 N B) := by
  let U:=memory T D S M W u
  have grid:=memory_grid ctx u
  obtain ⟨t,pt,first⟩:=guard_run grid room len1 (guard_actual m)
  by_cases zero : n=0
  · rw [if_pos zero] at first ⊢
    exact ⟨t,by nlinarith,path_native first fit⟩
  · rw [if_neg zero] at first ⊢
    obtain ⟨s,ps,last⟩:=copy_restore m grid room len1 len2 len8 small bound
      (memory_unary ctx u (by decide) (by decide) (by decide) u2)
      (memory_unary ctx u (by decide) (by decide) (by decide) u1)
      (memory_unary ctx u (by decide) (by decide) (by decide) u8)
    rw [memory_counter ctx u 8 ell (by decide) (by decide) (by decide)] at last
    exact ⟨t+s,by nlinarith,path_native (first.append last) fit⟩

end FullBodyClosure
