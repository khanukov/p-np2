import FullBodyClosure.Invariant
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1
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
private abbrev counter : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Index "counter"
private abbrev put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Buffer "put"
private abbrev place : (Nat → Option Bool) → Nat → List Bool → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.BufferModel "place"
private abbrev ij : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.IndexLoop "ij"
private abbrev foldState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "foldState"
private abbrev foldRoute : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Invariant "foldRoute"
private abbrev hornerState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "hornerState"
private abbrev lookupState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Beta "lookupState"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Return "returnState"
private abbrev digit : Bool → Nat := by run_tac checkedFrom `FullBodyClosure.IndexSemantics "digit"
private abbrev accumulate : Nat → List Bool → Nat := by run_tac checkedFrom `FullBodyClosure.IndexSemantics "accumulate"
private abbrev PopBufferRows : Fin 7500 → Fin 7500 → (Bool → Fin 7500) → Prop := by run_tac checkedFrom `FullBodyClosure.Buffer "PopBufferRows"
private abbrev HornerRows : Fin 3 → Bool → Prop := by run_tac checkedFrom `FullBodyClosure.Index "HornerRows"
private abbrev TransferRows : Fin 3 → Prop := by run_tac checkedFrom `FullBodyClosure.IndexLoop "TransferRows"
private abbrev Costed : Nat → Nat → Node → Node → Prop := by run_tac checkedFrom `FullBodyClosure.IndexLoop "Costed"
private theorem keep : ∀ {P : Nat} (s q : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (mv : Move), h ≤ P → h' ≤ P → 4 ≤ s.val → SerializedBody.machine.step s (T h)=(q,T h,mv) → (match mv with | .left=>h-1 | .stay=>h | .right=>h+1)=h' → Path P 1 (node s h T) (node q h' T) := by run_tac checkedKernel "keep"
private theorem grid_mono : ∀ {D T},Grid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by run_tac checkedKernel "Grid.mono"
private theorem grid_blank : ∀ {D T},Grid D T → ∀ j,j ≤ 12 → T (D j)=none := by run_tac checkedKernel "Grid.blank"
private theorem grid_cells : ∀ {D T},Grid D T → ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b := by run_tac checkedKernel "Grid.cells"
private theorem grid_change : ∀ {D T},Grid D T → ∀ h b c,T h=some b → Grid D (put T h (some c)) := by run_tac checkedKernel "Grid.change_some"
private theorem counter_fixed : ∀ {D T j v},Unary D T j v → counter T D j v=T := by run_tac checkedFrom `FullBodyClosure.Invariant "counter_fixed"
private theorem counter_grid : ∀ {D T},Grid D T → ∀ j v,j < 12 → Grid D (counter T D j v) := by run_tac checkedFrom `FullBodyClosure.Index "counter_grid"
private theorem place_outside : ∀ (T : Nat → Option Bool) (a : Nat) (xs : List Bool) (i : Nat), (i<a ∨ a+2*xs.length ≤ i) → place T a xs i=T i := by run_tac checkedFrom `FullBodyClosure.BufferModel "place_outside"
private theorem place_pair : ∀ (T : Nat → Option Bool) (a : Nat) (xs : List Bool),∀ j,(hj : j<xs.length) → place T a xs (a+2*j)=some true ∧ place T a xs (a+2*j+1)=some (xs[j]'hj) := by run_tac checkedFrom `FullBodyClosure.BufferModel "place_pair"
private theorem place_pop : ∀ (T : Nat → Option Bool) (a : Nat) (xs : List Bool) (b : Bool),T (a+2*xs.length)=some false → T (a+2*xs.length+1)=some false → put (put (place T a (xs++[b])) (a+2*xs.length+1) (some false)) (a+2*xs.length) (some false)=place T a xs := by run_tac checkedFrom `FullBodyClosure.BufferModel "place_pop"
private theorem pop_actual : ∀ m,PopBufferRows (foldRoute m) (lookupState m) (hornerState m) := by run_tac checkedFrom `FullBodyClosure.Invariant "pop_buffer_actual"
private theorem fold_jump : ∀ m,SerializedBody.machine.step (foldState m) none=(foldRoute m,none,.stay) := by run_tac checkedFrom `FullBodyClosure.Invariant "fold_jump"
private theorem fold_safe : ∀ m,4 ≤ (foldState m).val := by run_tac checkedFrom `FullBodyClosure.Invariant "fold_safe"
private theorem pop_path : ∀ {D T P d start lookup out},Grid D T → D 12 ≤ P → D 9+2*(d+1)+1 ≤ D 10 → (∀ j,j<d+1 → T (D 9+1+2*j)=some true ∧ ∃ b,T (D 9+1+2*j+1)=some b) → T (D 9+1+2*(d+1))≠some true → ∀ b,T (D 9+2*d+2)=some b → PopBufferRows start lookup out → Path P (2*(D 9-D 0)+4*d+25) (node start (D 0) T) (node (out b) (D 0) (put (put T (D 9+2*d+2) (some false)) (D 9+2*d+1) (some false))) := by run_tac checkedFrom `FullBodyClosure.Buffer "pop_buffer_path"
private theorem horner_run : ∀ {D T P n} (m : Fin 3) (b : Bool),Grid D T → D 12 ≤ P → D 2=D 1+n+1 → D 9=D 8+n+1 → HornerRows m b → TransferRows m → ∀ i j,i ≤ n → j < n → let value:=2*i+j+(if b then 1 else 0); if value < n then Costed P (512*(i+n+1)*(P+1)) (node (hornerState m b) (D 0) (ij T D i j)) (node (foldState m) (D 0) (ij T D value 0)) else ∃ left,left ≤ i ∧ Costed P (512*(i+n+1)*(P+1)) (node (hornerState m b) (D 0) (ij T D i j)) (node (SerializedBodyRefinement.getAbort m) (D 0) (ij T D left n)) := by run_tac checkedFrom `FullBodyClosure.IndexLoop "horner_run"
private theorem horner_actual (m : Fin 3) (b : Bool) : HornerRows m b := by
  fin_cases m <;> cases b
  · run_tac checkedFrom `FullBodyClosure.IndexRows0 "hornerCode0_0"
  · run_tac checkedFrom `FullBodyClosure.IndexRows0 "hornerCode0_1"
  · run_tac checkedFrom `FullBodyClosure.IndexRows1 "hornerCode1_0"
  · run_tac checkedFrom `FullBodyClosure.IndexRows1 "hornerCode1_1"
  · run_tac checkedFrom `FullBodyClosure.IndexRows2 "hornerCode2_0"
  · run_tac checkedFrom `FullBodyClosure.IndexRows2 "hornerCode2_1"
private theorem transfer_actual (m : Fin 3) : TransferRows m := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.IndexRows0 "transferCode0"
  · run_tac checkedFrom `FullBodyClosure.IndexRows1 "transferCode1"
  · run_tac checkedFrom `FullBodyClosure.IndexRows2 "transferCode2"
private theorem accumulate_ge : ∀ a bits,a ≤ accumulate a bits := by run_tac checkedFrom `FullBodyClosure.IndexSemantics "accumulate_ge"
private theorem fold_empty_lookup : ∀ {D T P H Q F n} (m : Fin 3),Grid D T → H ≤ D 0 → D 0=F+1 → D 12 ≤ P → D 2=D 1+n+1 → 0 < Q → H+Q < F → n < H → T H=none → T F=some false → (∀ i,H < i → i ≤ H+Q → T i=some true) → (∀ i,H+Q < i → i < F → T i=none) → ∀ (beta : Fin n → Bool),(∀ j : Fin n,T (H-1-j.val)=some (beta j)) → ∀ index : Fin n,Unary D T 1 index.val → T (D 9+1)≠some true → ∃ t,t ≤ 512*(n+1)*(P+1) ∧ Path P t (node (foldState m) (D 0) T) (node (returnState m (beta index)) (D 0) (counter T D 1 0)) := by run_tac checkedFrom `FullBodyClosure.Invariant "fold_empty_lookup"

-- Complete buffer folding proof follows; no new runtime table is introduced.
private theorem counter_put {T : Nat → Option Bool} {D : Nat → Nat} {j v h b}
    (away : ¬(D j < h ∧ h < D (j+1))) :
    counter (put T h b) D j v=put (counter T D j v) h b := by
  funext i
  change (if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else if i=h then b else T i)=
    (if i=h then b else if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else T i)
  by_cases eq : i=h
  · subst i;simp only [if_neg away]
  · simp only [if_neg eq]
private theorem place_counter {D : Nat → Nat} (j v : Nat) (bits : List Bool)
    (T : Nat → Option Bool) (a : Nat) (before : D (j+1) ≤ a) :
    place (counter T D j v) a bits=counter (place T a bits) D j v := by
  induction bits generalizing T a with
  | nil => rfl
  | cons b bs ih =>
    change place (put (put (counter T D j v) a (some true)) (a+1) (some b)) (a+2) bs=_
    rw [←counter_put (by omega : ¬(D j < a ∧ a < D (j+1))),
      ←counter_put (by omega : ¬(D j < a+1 ∧ a+1 < D (j+1))),ih _ _ (by omega)]
    rfl
private theorem place_grid {D T} (grid : Grid D T) (a : Nat) (bits : List Bool)
    (low : D 9 < a) (high : a+2*bits.length ≤ D 10) : Grid D (place T a bits) := by
  induction bits generalizing T a with
  | nil => exact grid
  | cons b bs ih =>
    have upper : a+1 < D 10 := by simp only [List.length_cons] at high;omega
    obtain ⟨old,cell⟩:=grid_cells grid 9 a (by decide) low (by change a<D 10;omega)
    have first:=grid_change grid a old true cell
    obtain ⟨old',cell'⟩:=grid_cells first 9 (a+1) (by decide) (by omega) upper
    have second:=grid_change first (a+1) old' b cell'
    change Grid D (place (put (put T a (some true)) (a+1) (some b)) (a+2) bs)
    exact ih second (a+2) (by omega) (by simp only [List.length_cons] at high;omega)
private theorem place_unary {D T j v} (grid : Grid D T) (unary : Unary D T j v)
    (j8 : j ≤ 8) (bits : List Bool) : Unary D (place T (D 9+1) bits) j v := by
  intro i lo hi
  have before:=grid_mono grid (j+1) 9 (by omega) (by decide)
  rw [place_outside T _ bits i (Or.inl (by omega))]
  exact unary i lo hi
private theorem place_below {D T} (grid : Grid D T) (bits : List Bool) (i : Nat) (low : i < D 0) :
    place T (D 9+1) bits i=T i :=
  place_outside T _ bits i (Or.inl (by have :=grid_mono grid 0 9 (by decide) (by decide);omega))
private theorem place_ninth {D T r} (grid : Grid D T) (len : D 10=D 9+2*r+1)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false) (bits : List Bool) (fit : bits.length ≤ r) :
    place T (D 9+1) bits (D 9+1+2*bits.length)≠some true := by
  rw [place_outside T _ bits _ (Or.inr (by omega))]
  by_cases full : bits.length=r
  · rw [show D 9+1+2*bits.length=D 10 by omega,grid_blank grid 10 (by decide)]
    decide
  · rw [free _ (by omega) (by omega)];decide
private theorem place_counter_zero {D T} (grid : Grid D T) (zero : Unary D T 8 0) (bits : List Bool) (a : Nat) :
    ij (place T (D 9+1) bits) D a 0=place (counter T D 1 a) (D 9+1) bits := by
  change counter (counter (place T (D 9+1) bits) D 8 0) D 1 a=_
  rw [counter_fixed (place_unary grid zero (by decide) bits)]
  exact (place_counter 1 a bits T _ (by change D 2 ≤ D 9+1;have :=grid_mono grid 2 9 (by decide) (by decide);omega)).symm
private theorem pop_digit {D T P r} (m : Fin 3) (grid : Grid D T) (room : D 12 ≤ P)
    (len9 : D 10=D 9+2*r+1) (free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (a : Nat) (bits : List Bool) (b : Bool) (fit : bits.length+1 ≤ r) :
    ∃ t,t ≤ 64*(P+1) ∧ Path P t
      (node (foldState m) (D 0) (place (counter T D 1 a) (D 9+1) (bits++[b])))
      (node (hornerState m b) (D 0) (place (counter T D 1 a) (D 9+1) bits)) := by
  let U:=counter T D 1 a
  have gU : Grid D U:=counter_grid grid 1 a (by decide)
  have unmodified (i : Nat) (lo : D 9 < i) : U i=T i := by
    have order:=grid_mono grid 2 9 (by decide) (by decide)
    change (if D 1 < i ∧ i < D 2 then _ else T i)=T i
    exact if_neg (by omega)
  have freeU (i : Nat) (lo : D 9 < i) (hi : i < D 10) : U i=some false := by rw [unmodified i lo];exact free i lo hi
  let V:=place U (D 9+1) (bits++[b])
  have gV : Grid D V:=place_grid gU (D 9+1) (bits++[b]) (by omega) (by simp only [List.length_append,List.length_singleton];omega)
  have start:=keep (foldState m) (foldRoute m) (D 0) (D 0) V .stay (P:=P)
    (by have :=grid_mono grid 0 12 (by decide) (by decide);omega)
    (by have :=grid_mono grid 0 12 (by decide) (by decide);omega) (fold_safe m)
    (by rw [grid_blank gV 0 (by decide)];exact fold_jump m) rfl
  have middle:=pop_path gV room (d:=bits.length) (by omega)
    (by intro j hj;exact ⟨(place_pair U _ (bits++[b]) j (by simp;omega)).1,_,(place_pair U _ (bits++[b]) j (by simp;omega)).2⟩)
    (by simpa only [List.length_append,List.length_singleton] using place_ninth gU len9 freeU (bits++[b]) (by simp;omega)) b
    (by
      have pair:=(place_pair U (D 9+1) (bits++[b]) bits.length (by simp)).2
      have val : (bits++[b])[bits.length]'(by simp)=b := by simp
      rw [val] at pair
      simpa only [show D 9+1+2*bits.length+1=D 9+2*bits.length+2 by omega] using pair)
    (pop_actual m)
  have fixed:=place_pop U (D 9+1) bits b
    (freeU _ (by omega) (by omega)) (freeU _ (by omega) (by omega))
  have coords : D 9+2*bits.length+2=D 9+1+2*bits.length+1 := by omega
  have coords' : D 9+2*bits.length+1=D 9+1+2*bits.length := by omega
  rw [coords,coords',fixed] at middle
  have path:=start.append middle
  refine ⟨_,?_,path⟩
  have upper:=grid_mono grid 10 12 (by decide) (by decide)
  omega
private theorem fold_empty : ∀ {D T P} (m : Fin 3),Grid D T → D 12 ≤ P →
    T (D 9+1)≠some true → ∃ t,t ≤ 32*(P+1) ∧ Path P t
      (node (foldState m) (D 0) T) (node (lookupState m) (D 0) T) := by
  run_tac checkedFrom `FullBodyClosure.Invariant "fold_empty"
private theorem fold_price (P n a d s t u : Nat) (ha : a<n)
    (hs : s ≤ 64*(P+1)) (ht : t ≤ 512*(a+n+1)*(P+1))
    (hu : u ≤ 2048*(d+1)*(n+1)*(P+1)) :
    s+t+u ≤ 2048*(d+2)*(n+1)*(P+1) := by nlinarith
private theorem fold_digits {D T P n r} (m : Fin 3) (grid : Grid D T) (room : D 12 ≤ P)
    (len1 : D 2=D 1+n+1) (len8 : D 9=D 8+n+1) (len9 : D 10=D 9+2*r+1)
    (zero8 : Unary D T 8 0) (free : ∀ i,D 9 < i → i < D 10 → T i=some false) :
    ∀ (bits : List Bool) (a : Nat),bits.length ≤ r → a<n →
    ∃ t,t ≤ 2048*(bits.length+1)*(n+1)*(P+1) ∧
      if accumulate a bits < n then Path P t
        (node (foldState m) (D 0) (place (counter T D 1 a) (D 9+1) bits.reverse))
        (node (lookupState m) (D 0) (counter T D 1 (accumulate a bits)))
      else ∃ (rest : List Bool) (left : Nat),rest.length ≤ bits.length ∧ left ≤ n ∧ Path P t
        (node (foldState m) (D 0) (place (counter T D 1 a) (D 9+1) bits.reverse))
        (node (SerializedBodyRefinement.getAbort m) (D 0) (ij (place T (D 9+1) rest) D left n)) := by
  intro bits
  induction bits with
  | nil =>
    intro a _len ha
    obtain ⟨t,price,path⟩:=fold_empty m (counter_grid grid 1 a (by decide)) room (by
      have order:=grid_mono grid 2 9 (by decide) (by decide)
      have stop:=place_ninth grid len9 free [] (by simp)
      change T (D 9+1)≠some true at stop
      change (if D 1 < D 9+1 ∧ D 9+1 < D 2 then _ else T (D 9+1))≠some true
      rw [if_neg (by omega : ¬(D 1 < D 9+1 ∧ D 9+1 < D 2))];exact stop)
    refine ⟨t,?_,?_⟩
    · simp only [List.length_nil];nlinarith
    · change if a<n then _ else _
      rw [if_pos ha]
      exact path
  | cons b bs ih =>
    intro a length ha
    simp only [List.length_cons] at length
    obtain ⟨s,ps,first⟩:=pop_digit m grid room len9 free a bs.reverse b (by simpa using length)
    change Path P s (node (foldState m) (D 0) (place (counter T D 1 a) (D 9+1) (bs.reverse++[b]))) _ at first
    have gBase:=place_grid grid (D 9+1) bs.reverse (by omega) (by simp only [List.length_reverse];omega)
    have native:=horner_run m b gBase room len1 len8 (horner_actual m b) (transfer_actual m) a 0 (by omega) (by omega)
    have init:=place_counter_zero grid zero8 bs.reverse a
    dsimp only at native
    let value:=2*a+(if b then 1 else 0)
    change (if value<n then _ else _) at native
    have eval : accumulate a (b::bs)=accumulate value bs := rfl
    by_cases safe : value<n
    · rw [if_pos safe] at native
      obtain ⟨t,pt,middle⟩:=native
      change Path P t (node (hornerState m b) (D 0) (ij (place T (D 9+1) bs.reverse) D a 0))
        (node (foldState m) (D 0) (ij (place T (D 9+1) bs.reverse) D value 0)) at middle
      rw [init,place_counter_zero grid zero8 bs.reverse value] at middle
      obtain ⟨u,pu,last⟩:=ih value (by omega) safe
      refine ⟨s+t+u,?_,?_⟩
      · simp only [List.length_cons]
        exact fold_price P n a bs.length s t u ha ps pt pu
      · rw [eval]
        by_cases final : accumulate value bs<n
        · rw [if_pos final] at last ⊢
          simpa only [List.reverse_cons] using (first.append middle).append last
        · rw [if_neg final] at last ⊢
          obtain ⟨rest,left,lr,ll,path⟩:=last
          exact ⟨rest,left,by simp only [List.length_cons];omega,ll,by simpa only [List.reverse_cons] using (first.append middle).append path⟩
    · rw [if_neg safe] at native
      obtain ⟨left,le,t,pt,last⟩:=native
      rw [init] at last
      have failed : ¬accumulate value bs<n := by have :=accumulate_ge value bs;omega
      refine ⟨s+t,?_,?_⟩
      · simpa only [List.length_cons,Nat.add_zero] using fold_price P n a bs.length s t 0 ha ps pt (by omega)
      · rw [eval,if_neg failed]
        refine ⟨bs.reverse,left,by simpa only [List.length_reverse,List.length_cons] using Nat.le_succ bs.length,by omega,?_⟩
        simpa only [List.reverse_cons] using first.append last

private abbrev lookupLoopState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Beta "lookupLoopState"
private abbrev BetaLiftRows : Fin 7500 → (Bool → Fin 7500) → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "BetaLiftRows"
private abbrev LookupRows : Fin 3 → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "LookupRows"
private theorem beta_lift_actual (m : Fin 3) : BetaLiftRows (lookupState m) (lookupLoopState m) := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.BetaRows0 "betaLiftCode0"
  · run_tac checkedFrom `FullBodyClosure.BetaRows1 "betaLiftCode1"
  · run_tac checkedFrom `FullBodyClosure.BetaRows2 "betaLiftCode2"
private theorem beta_loop_actual (m : Fin 3) : LookupRows m := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.BetaRows0 "lookupCode0"
  · run_tac checkedFrom `FullBodyClosure.BetaRows1 "lookupCode1"
  · run_tac checkedFrom `FullBodyClosure.BetaRows2 "lookupCode2"
private theorem beta_lookup : ∀ {T D H Q F P n} (m : Fin 3),Grid D T → H  ≤  D 0 → D 0=F+1 →
    D 12  ≤  P → D 2=D 1+n+1 → 0 < Q → H+Q < F → n < H → T H=none → T F=some false →
    (∀ i,H < i → i  ≤  H+Q → T i=some true) → (∀ i,H+Q < i → i < F → T i=none) →
    ∀ (beta : Fin n → Bool),(∀ j : Fin n,T (H-1-j.val)=some (beta j)) → ∀ index : Fin n,
    BetaLiftRows (lookupState m) (lookupLoopState m) → LookupRows m →
    ∃ t,t  ≤  256*(n+1)*(P+1) ∧ Path P t (node (lookupState m) (D 0) (counter T D 1 index.val))
      (node (returnState m (beta index)) (D 0) (counter T D 1 0)) := by run_tac checkedFrom `FullBodyClosure.Beta "beta_lookup"
private abbrev numeral : List Bool → Nat := by run_tac checkedFrom `FullBodyClosure.IndexSemantics "numeral"
private theorem reverse_horner : ∀ bits,accumulate 0 bits.reverse=numeral bits := by
  run_tac checkedFrom `FullBodyClosure.IndexSemantics "reverse_horner"
private theorem fold_lookup_price (P n d t u : Nat)
    (ht : t ≤ 2048*(d+1)*(n+1)*(P+1)) (hu : u ≤ 256*(n+1)*(P+1)) :
    t+u ≤ 4096*(d+1)*(n+1)*(P+1) := by nlinarith
/-- Complete native reverse-buffer operand consumer and canonical physical beta lookup.
The source/assignment/exterior are those of T; failure is still the live cleanup entry. -/
private theorem fold_and_lookup {D T P H Q F n r} (m : Fin 3) (grid : Grid D T)
    (before : H ≤ D 0) (d0 : D 0=F+1) (room : D 12 ≤ P)
    (len1 : D 2=D 1+n+1) (len8 : D 9=D 8+n+1) (len9 : D 10=D 9+2*r+1)
    (zero1 : Unary D T 1 0) (zero8 : Unary D T 8 0)
    (free : ∀ i,D 9 < i → i < D 10 → T i=some false)
    (positive : 0 < Q) (arena : H+Q < F) (hn : n < H) (header : T H=none) (fence : T F=some false)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (beta : Fin n → Bool) (cells : ∀ j : Fin n,T (H-1-j.val)=some (beta j))
    (payload : List Bool) (length : payload.length ≤ r) (nonzero : 0 < n) :
    ∃ t,t ≤ 4096*(payload.length+1)*(n+1)*(P+1) ∧
      if inside : numeral payload<n then Path P t
        (node (foldState m) (D 0) (place T (D 9+1) payload))
        (node (returnState m (beta ⟨numeral payload,inside⟩)) (D 0) T)
      else ∃ (rest : List Bool) (left : Nat),rest.length ≤ payload.length ∧ left ≤ n ∧ Path P t
        (node (foldState m) (D 0) (place T (D 9+1) payload))
        (node (SerializedBodyRefinement.getAbort m) (D 0) (ij (place T (D 9+1) rest) D left n)) := by
  obtain ⟨t,price,path⟩:=fold_digits m grid room len1 len8 len9 zero8 free payload.reverse 0
    (by simpa using length) nonzero
  rw [counter_fixed zero1,List.reverse_reverse,reverse_horner] at path
  simp only [List.length_reverse] at price
  by_cases inside : numeral payload<n
  · rw [if_pos inside] at path
    obtain ⟨u,price',last⟩:=beta_lookup m grid before d0 room len1 positive arena hn header fence marks gap
      beta cells ⟨numeral payload,inside⟩ (beta_lift_actual m) (beta_loop_actual m)
    rw [counter_fixed zero1] at last
    refine ⟨t+u,fold_lookup_price P n payload.length t u price price',?_⟩
    simpa only [dif_pos inside] using path.append last
  · rw [if_neg inside] at path
    obtain ⟨rest,left,lr,ll,path⟩:=path
    refine ⟨t,?_,?_⟩
    · nlinarith
    · simp only [dif_neg inside]
      exact ⟨rest,left,by simpa using lr,ll,path⟩
end FullBodyClosure
