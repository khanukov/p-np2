import FullBodyClosure.Input
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
    (Fin S → Bool) → (Fin n → Bool) → Prop := by run_tac checkedFrom `FullBodyClosure.Input "Context"
private abbrev memory : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Input "memory"
private abbrev counter : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Input "counter"
private abbrev place : (Nat → Option Bool) → Nat → List Bool → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Input "place"
private abbrev ij : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Fold "ij"
private abbrev readState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Input "readState"
private abbrev inputState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Input "inputState"
private abbrev foldState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Fold "foldState"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Fold "returnState"
private abbrev numeral : List Bool → Nat := by run_tac checkedFrom `FullBodyClosure.Fold "numeral"
private theorem Context.grid : ∀ {D T S L H Q F r M W n source beta},Context D T S L H Q F r M W n source beta → Grid D T := by run_tac checkedFrom `FullBodyClosure.Input "Context.grid"
private theorem Context.before : ∀ {D T S L H Q F r M W n source beta},Context D T S L H Q F r M W n source beta → S < D 0 := by run_tac checkedFrom `FullBodyClosure.Input "Context.before"
private theorem memory_below : ∀ {T D S M W u i},(∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) → i < D 0 →
    memory T D S M W u i=(if i=M+u ∧ i < S then none else T i) := by run_tac checkedFrom `FullBodyClosure.Input "memory_below"
private theorem memory_grid : ∀ {D T S L H Q F r M W n source beta}
    (_ctx : Context D T S L H Q F r M W n source beta) (u : Nat) , Grid D (memory T D S M W u) := by run_tac checkedFrom `FullBodyClosure.Input "memory_grid"
private theorem memory_unary : ∀ {D T S L H Q F r M W n source beta j v}
    (_ctx : Context D T S L H Q F r M W n source beta) (u : Nat)
    (_hj : j < 12) (_ne4 : j≠4) (_ne11 : j≠11) (_unary : Unary D T j v) , Unary D (memory T D S M W u) j v := by run_tac checkedFrom `FullBodyClosure.Input "memory_unary"
private theorem memory_place : ∀ {D T S L H Q F r M W n source beta}
    (_ctx : Context D T S L H Q F r M W n source beta) (a u : Nat) (bits : List Bool)
    (_lo : D 9 < a) (_hi : a+2*bits.length ≤ D 10) , place (memory T D S M W u) a bits=memory (place T a bits) D S M W u := by run_tac checkedFrom `FullBodyClosure.Input "memory_place"
private theorem memory_buffer : ∀ {D T S L H Q F r M W n source beta}
    (_ctx : Context D T S L H Q F r M W n source beta) (u i : Nat)
    (_lo : D 9 < i) (_hi : i < D 10) , memory T D S M W u i=T i := by run_tac checkedFrom `FullBodyClosure.Input "memory_buffer"
private theorem place_counter : ∀ {D : Nat → Nat} (j v : Nat) (bits : List Bool) (T : Nat → Option Bool)
    (a : Nat),D (j+1) ≤ a → place (counter T D j v) a bits=counter (place T a bits) D j v := by run_tac checkedFrom `FullBodyClosure.Input "place_counter"
private theorem counter_fixed : ∀ {D T j v},Unary D T j v → counter T D j v=T := by run_tac checkedFrom `FullBodyClosure.Fold "counter_fixed"
private theorem path_native : ∀ {N B P t a b} (path : Path P t a b) (fit : P < tapeLength N B) , Native t (embed a (lt_of_le_of_lt path.bounds.1 fit)) (embed b (lt_of_le_of_lt path.bounds.2 fit)) := by run_tac checkedFrom `FullBodyClosure.Input "path_native"
private theorem index_read : ∀ {D T S L H Q F r M W n source beta}
    (_ctx : Context D T S L H Q F r M W n source beta) (N B P : Nat)
    (_len8 : D 9=D 8+n+1) (_len9 : D 10=D 9+2*r+1)
    (_free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (_room : D 12 ≤ P) (_fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) , ∀ j u (bits : List Bool),j ≤ n → bits.length+j ≤ r → u+j ≤ W →
    ∃ t,t ≤ 256*(j+1)*(P+1) ∧ Native t
      (⟨readState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) bits) D 8 j) D S M W u i.val⟩ : Config 7500 N B)
      (⟨foldState (SerializedBody.sourceMode source (M+(u+j))),⟨D 0,h0⟩,
        fun i=>memory (counter (place T (D 9+1) (bits++SerializedBody.window source (M+u) j)) D 8 0)
          D S M W (u+j) i.val⟩ : Config 7500 N B) := by run_tac checkedFrom `FullBodyClosure.Input "index_read"
private theorem index_read_total : ∀ {D T S L H Q F r M W n source beta}
    (_ctx : Context D T S L H Q F r M W n source beta) (N B P : Nat)
    (_len8 : D 9=D 8+n+1) (_len9 : D 10=D 9+2*r+1)
    (_free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (_room : D 12 ≤ P) (_fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B)
    (j u : Nat) (bits : List Bool) (_hn : j ≤ n) (_capacity : bits.length+j ≤ r) (_cursor : u ≤ W) , let count:=min j (W-u)
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
          fun i=>memory (counter (place T (D 9+1) payload) D 8 (j-count-1)) D S M W (u+count) i.val⟩ : Config 7500 N B) := by run_tac checkedFrom `FullBodyClosure.Input "index_read_total"
private theorem prepare_index : ∀ {D T S L H Q F r M W n source beta}
    (_ctx : Context D T S L H Q F r M W n source beta) (u N B P ell : Nat) (m : Fin 3)
    (_len1 : D 2=D 1+n+1) (_len2 : D 3=D 2+r+1) (_len8 : D 9=D 8+n+1)
    (_small : ell ≤ n) (_bound : ell ≤ r) (_u2 : Unary D T 2 ell) (_u1 : Unary D T 1 0) (_u8 : Unary D T 8 0)
    (_room : D 12 ≤ P) (_fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) , ∃ t,t ≤ 512*(ell+1)*(P+1) ∧ Native t
      (⟨inputState m,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (if n=0 then ⟨SerializedBodyRefinement.getAbort m,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
       else ⟨readState m,⟨D 0,h0⟩,fun i=>memory (counter T D 8 ell) D S M W u i.val⟩ : Config 7500 N B) := by run_tac checkedFrom `FullBodyClosure.Input "prepare_index"
private theorem fold_and_lookup : ∀ {D T P H Q F n r} (m : Fin 3) (_grid : Grid D T)
    (_before : H ≤ D 0) (_d0 : D 0=F+1) (_room : D 12 ≤ P)
    (_len1 : D 2=D 1+n+1) (_len8 : D 9=D 8+n+1) (_len9 : D 10=D 9+2*r+1)
    (_zero1 : Unary D T 1 0) (_zero8 : Unary D T 8 0)
    (_free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (_positive : 0 < Q) (_arena : H+Q < F) (_hn : n < H) (_header : T H=none) (_fence : T F=some false)
    (_marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (_gap : ∀ i,H+Q < i → i < F → T i=none)
    (beta : Fin n → Bool) (_cells : ∀ j : Fin n,T (H-1-j.val)=some (beta j))
    (payload : List Bool) (_length : payload.length ≤ r) (_nonzero : 0 < n) , ∃ t,t ≤ 4096*(payload.length+1)*(n+1)*(P+1) ∧
      if inside : numeral payload<n then Path P t
        (node (foldState m) (D 0) (place T (D 9+1) payload))
        (node (returnState m (beta ⟨numeral payload,inside⟩)) (D 0) T)
      else ∃ (rest : List Bool) (left : Nat),rest.length ≤ payload.length ∧ left ≤ n ∧ Path P t
        (node (foldState m) (D 0) (place T (D 9+1) payload))
        (node (SerializedBodyRefinement.getAbort m) (D 0) (ij (place T (D 9+1) rest) D left n)) := by run_tac checkedFrom `FullBodyClosure.Fold "fold_and_lookup"
private theorem memory_header {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u i : Nat)
    (lo : S ≤ i) (hi : i < D 0) : memory T D S M W u i=T i := by
  have grid:=ctx.grid
  rcases ctx with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
  rw [memory_below mono hi,if_neg (by omega : ¬(i=M+u ∧ i < S))]
private theorem operand_price (P n ell a b c : Nat)
    (ha : a ≤ 512*(ell+1)*(P+1)) (hb : b ≤ 256*(ell+1)*(P+1))
    (hc : c ≤ 4096*(ell+1)*(n+1)*(P+1)) :
    a+b+c ≤ 8192*(ell+1)*(n+1)*(P+1) := by nlinarith
private theorem fold_memory {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u N B P : Nat)
    (len1 : D 2=D 1+n+1) (len8 : D 9=D 8+n+1) (len9 : D 10=D 9+2*r+1)
    (u1 : Unary D T 1 0) (u8 : Unary D T 8 0)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (payload : List Bool) (length : payload.length ≤ r) (positiveN : 0 < n)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 4096*(payload.length+1)*(n+1)*(P+1) ∧
      if inside : numeral payload<n then Native t
        (⟨foldState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
          fun i=>place (memory T D S M W u) (D 9+1) payload i.val⟩ : Config 7500 N B)
        (⟨returnState (SerializedBody.sourceMode source (M+u)) (beta ⟨numeral payload,inside⟩),⟨D 0,h0⟩,
          fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      else ∃ (rest : List Bool) (left : Nat),rest.length ≤ payload.length ∧ left ≤ n ∧ Native t
        (⟨foldState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
          fun i=>place (memory T D S M W u) (D 9+1) payload i.val⟩ : Config 7500 N B)
        (⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
          fun i=>ij (place (memory T D S M W u) (D 9+1) rest) D left n i.val⟩ : Config 7500 N B) := by
  have grid:=memory_grid ctx u
  have fixed1:=memory_unary ctx u (by decide) (by decide) (by decide) u1
  have fixed8:=memory_unary ctx u (by decide) (by decide) (by decide) u8
  have ctx0:=ctx
  rcases ctx with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
  have hb : H < D 0 := by omega
  have header (i : Nat) (lo : S ≤ i) (hi : i < D 0) : memory T D S M W u i=T i := memory_header ctx0 u i lo hi
  obtain ⟨t,price,path⟩:=fold_and_lookup (SerializedBody.sourceMode source (M+u)) grid (by omega) anchor room len1 len8 len9
    fixed1 fixed8 (by intro i lo hi;rw [memory_buffer ctx0 u i lo hi];exact free i lo hi)
    positive arena (by omega) (by rw [header H (by omega) hb];exact right)
    (by rw [header F (by omega) (by omega)];exact fence)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact gap i lo hi)
    beta (by intro j;rw [header (H-1-j.val) (by omega) (by omega)];exact betaCells j)
    payload length positiveN
  refine ⟨t,price,?_⟩
  by_cases inside : numeral payload<n
  · simp only [dif_pos inside] at path ⊢
    exact path_native path fit
  · simp only [dif_neg inside] at path ⊢
    obtain ⟨rest,left,lr,ll,path⟩:=path
    exact ⟨rest,left,lr,ll,path_native path fit⟩
/-- Connected full native input-node operand, including zero arity, logical
truncation and index overflow. A live abort is kept distinct from literal reject. -/
private theorem input_full {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u N B P ell : Nat)
    (len1 : D 2=D 1+n+1) (len2 : D 3=D 2+r+1) (len8 : D 9=D 8+n+1) (len9 : D 10=D 9+2*r+1)
    (small : ell ≤ n) (bound : ell ≤ r) (u2 : Unary D T 2 ell) (u1 : Unary D T 1 0) (u8 : Unary D T 8 0)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false) (cursor : u ≤ W)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let start : Config 7500 N B:=⟨inputState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
      fun i=>memory T D S M W u i.val⟩
    let payload:=SerializedBody.window source (M+u) ell
    ∃ t,t ≤ 8192*(ell+1)*(n+1)*(P+1) ∧
      if n=0 then Native t start
        ⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
      else if ell ≤ W-u then
        if inside : numeral payload<n then Native t start
          ⟨returnState (SerializedBody.sourceMode source (M+(u+ell))) (beta ⟨numeral payload,inside⟩),⟨D 0,h0⟩,
            fun i=>memory T D S M W (u+ell) i.val⟩
        else ∃ (rest : List Bool) (left : Nat),rest.length ≤ ell ∧ left ≤ n ∧ Native t start
          ⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+(u+ell))),⟨D 0,h0⟩,
            fun i=>ij (place (memory T D S M W (u+ell)) (D 9+1) rest) D left n i.val⟩
      else Native t start
        ⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+W)),⟨D 0,h0⟩,
          fun i=>memory (counter (place T (D 9+1) (SerializedBody.window source (M+u) (W-u))) D 8 (ell-(W-u)-1))
            D S M W W i.val⟩ := by
  dsimp only
  obtain ⟨a,pa,first⟩:=prepare_index ctx u N B P ell (SerializedBody.sourceMode source (M+u))
    len1 len2 len8 small bound u2 u1 u8 room fit h0
  by_cases zero : n=0
  · rw [if_pos zero] at first
    refine ⟨a,?_,?_⟩
    · nlinarith
    · simp only [if_pos zero];exact first
  · rw [if_neg zero] at first
    by_cases enough : ell ≤ W-u
    · obtain ⟨b,pb,second⟩:=index_read ctx N B P len8 len9 free room fit h0 ell u [] small (by simpa using bound) (by omega)
      simp only [List.nil_append] at second
      have clean : memory (counter (place T (D 9+1) (SerializedBody.window source (M+u) ell)) D 8 0) D S M W (u+ell)=
          place (memory T D S M W (u+ell)) (D 9+1) (SerializedBody.window source (M+u) ell) := by
        rw [←place_counter 8 0 _ T _ (by change D 9 ≤ D 9+1;omega),counter_fixed u8,
          ←memory_place ctx (D 9+1) (u+ell) _ (by omega) (by simp only [SerializedBody.window,List.length_ofFn];omega)]
      rw [clean] at second
      obtain ⟨c,pc,last⟩:=fold_memory ctx (u+ell) N B P len1 len8 len9 u1 u8 free
        (SerializedBody.window source (M+u) ell) (by simpa only [SerializedBody.window,List.length_ofFn] using bound)
        (by omega) room fit h0
      simp only [SerializedBody.window,List.length_ofFn] at pc
      refine ⟨a+b+c,operand_price P n ell a b c pa pb pc,?_⟩
      simp only [if_neg zero,if_pos enough]
      by_cases inside : numeral (SerializedBody.window source (M+u) ell)<n
      · simp only [dif_pos inside] at last ⊢
        exact native_trans (native_trans first second) last
      · simp only [dif_neg inside] at last ⊢
        obtain ⟨rest,left,lr,ll,last⟩:=last
        exact ⟨rest,left,by simpa only [SerializedBody.window,List.length_ofFn] using lr,ll,
          native_trans (native_trans first second) last⟩
    · obtain ⟨b,pb,last⟩:=index_read_total ctx N B P len8 len9 free room fit h0 ell u [] small
        (by simpa using bound) cursor
      simp only [if_neg enough,min_eq_right (by omega : W-u ≤ ell),List.nil_append] at last
      have finish : u+(W-u)=W := by omega
      rw [finish] at last
      refine ⟨a+b,?_,?_⟩
      · nlinarith
      · simp only [if_neg zero,if_neg enough]
        exact native_trans first last

end FullBodyClosure
