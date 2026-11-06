import FullBodyClosure.Operand
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
private abbrev put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by run_tac checkedKernel "put"
private abbrev recordBit : Fin 7 → Nat → Bool := by run_tac checkedFrom `FullBodyClosure.Representation "recordBit"
private theorem record_not_free : ∀ c : Fin 7,(recordBit c 0 && recordBit c 1 && recordBit c 2)=false := by run_tac checkedFrom `FullBodyClosure.Representation "record_not_free"
private def recordCell (K : List (Fin 7)) (j b : Nat) : Bool :=
  match K[j]? with | some c=>recordBit c b | none=>true
private def StackCells (D : Nat → Nat) (T : Nat → Option Bool) (r : Nat) (K : List (Fin 7)) : Prop :=
  ∀ j,j ≤ r → ∀ b,b < 3 → T (D 10+1+3*j+b)=some (recordCell K j b)
private def recordWrite (T : Nat → Option Bool) (a : Nat) (b0 b1 b2 : Bool) : Nat → Option Bool :=
  put (put (put T (a+2) (some b2)) (a+1) (some b1)) a (some b0)
private theorem recordWrite_at (T : Nat → Option Bool) (a : Nat) (c : Fin 7) (b : Nat) (hb : b < 3) :
    recordWrite T a (recordBit c 0) (recordBit c 1) (recordBit c 2) (a+b)=some (recordBit c b) := by
  interval_cases b
  · change (if a+0=a then _ else _)=some (recordBit c 0)
    exact if_pos (by omega)
  · change (if a+1=a then _ else if a+1=a+1 then _ else _)=some (recordBit c 1)
    rw [if_neg (by omega : a+1≠a),if_pos rfl]
  · change (if a+2=a then _ else if a+2=a+1 then _ else if a+2=a+2 then _ else _)=some (recordBit c 2)
    rw [if_neg (by omega : a+2≠a),if_neg (by omega : a+2≠a+1),if_pos rfl]
private theorem recordWrite_true (T : Nat → Option Bool) (a b : Nat) (hb : b < 3) :
    recordWrite T a true true true (a+b)=some true := by
  interval_cases b
  · change (if a+0=a then _ else _)=some true
    exact if_pos (by omega)
  · change (if a+1=a then _ else if a+1=a+1 then _ else _)=some true
    rw [if_neg (by omega : a+1≠a),if_pos rfl]
  · change (if a+2=a then _ else if a+2=a+1 then _ else if a+2=a+2 then _ else _)=some true
    rw [if_neg (by omega : a+2≠a),if_neg (by omega : a+2≠a+1),if_pos rfl]
private theorem recordWrite_outside (T : Nat → Option Bool) (a i : Nat) (b0 b1 b2 : Bool)
    (outside : i < a ∨ a+3 ≤ i) : recordWrite T a b0 b1 b2 i=T i := by
  change (if i=a then _ else if i=a+1 then _ else if i=a+2 then _ else T i)=T i
  rw [if_neg (by omega : i≠a),if_neg (by omega : i≠a+1),if_neg (by omega : i≠a+2)]
private theorem recordCell_free (K : List (Fin 7)) (j b : Nat) (hj : K.length ≤ j) : recordCell K j b=true := by
  rw [recordCell,List.getElem?_eq_none (by omega)]
private theorem list_append_old (K : List (Fin 7)) (c : Fin 7) (j : Nat) (hj : j < K.length) :
    (K++[c])[j]?=K[j]? := by
  induction K generalizing j with
  | nil => simp only [List.length_nil] at hj;omega
  | cons a K ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hj)
private theorem list_append_last (K : List (Fin 7)) (c : Fin 7) : (K++[c])[K.length]?=some c := by
  induction K with
  | nil => rfl
  | cons a K ih => exact ih
private theorem recordCell_last (K : List (Fin 7)) (c : Fin 7) (b : Nat) :
    recordCell (K++[c]) K.length b=recordBit c b := by rw [recordCell,list_append_last]
private theorem recordCell_old (K : List (Fin 7)) (c : Fin 7) (j b : Nat) (ne : j≠K.length) :
    recordCell (K++[c]) j b=recordCell K j b := by
  by_cases before : j < K.length
  · rw [recordCell,list_append_old K c j before]
    rfl
  · rw [recordCell_free (K++[c]) j b (by simp;omega),recordCell_free K j b (by omega)]
private theorem stack_push_cells {D T r K} (stack : StackCells D T r K) (c : Fin 7) :
    StackCells D (recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2)) r (K++[c]) := by
  intro j hj b hb
  by_cases last : j=K.length
  · subst j
    rw [recordCell_last]
    have coords : D 10+1+3*K.length+b=(D 10+3*K.length+1)+b := by omega
    rw [coords]
    exact recordWrite_at T _ c b hb
  · rw [recordWrite_outside T _ _ _ _ _ (by omega),stack j hj b hb,recordCell_old K c j b last]
private theorem stack_pop_cells {D T r K} (c : Fin 7) (stack : StackCells D T r (K++[c])) :
    StackCells D (recordWrite T (D 10+3*K.length+1) true true true) r K := by
  intro j hj b hb
  by_cases last : j=K.length
  · subst j
    rw [recordCell_free K K.length b le_rfl]
    have coords : D 10+1+3*K.length+b=(D 10+3*K.length+1)+b := by omega
    rw [coords]
    exact recordWrite_true T _ b hb
  · rw [recordWrite_outside T _ _ _ _ _ (by omega),stack j hj b hb,recordCell_old K c j b last]
private theorem stack_busy {D T r K} (stack : StackCells D T r K) (bound : K.length ≤ r) :
    ∀ j,j < K.length → ∃ a b c : Bool,(a && b && c)=false ∧
      T (D 10+1+3*j)=some a ∧ T (D 10+1+3*j+1)=some b ∧ T (D 10+1+3*j+2)=some c := by
  intro j hj
  let code:Fin 7:=K[j]'hj
  have get : K[j]?=some code := by simp [code,hj]
  have h0:=stack j (by omega) 0 (by decide)
  have h1:=stack j (by omega) 1 (by decide)
  have h2:=stack j (by omega) 2 (by decide)
  simp only [recordCell,get,Nat.add_zero] at h0 h1 h2
  exact ⟨recordBit code 0,recordBit code 1,recordBit code 2,record_not_free code,h0,h1,h2⟩
private abbrev PushRows : Fin 7500 → Fin 7500 → Bool → Bool → Bool → Prop := by run_tac checkedFrom `FullBodyClosure.Stack "PushRows"
private abbrev PopRows : Fin 3 → Bool → (Fin 7 → Fin 7500) → Prop := by run_tac checkedFrom `FullBodyClosure.Stack "PopRows"
private abbrev pushState : Fin 3 → Fin 7 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.StackRows "pushState"
private abbrev popNextState : Fin 3 → Bool → Fin 7 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.StackRows "popNextState"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Return "returnState"
private theorem push_path : ∀ {D T P start out d b0 b1 b2},Grid D T → D 12 ≤ P → D 10+3*d+4 ≤ D 11 →
    (∀ j,j < d → ∃ a b c : Bool,(a && b && c)=false ∧ T (D 10+1+3*j)=some a ∧ T (D 10+1+3*j+1)=some b ∧ T (D 10+1+3*j+2)=some c) →
    T (D 10+3*d+1)=some true → T (D 10+3*d+2)=some true → T (D 10+3*d+3)=some true →
    PushRows start out b0 b1 b2 → Path P (2*(D 10-D 0)+6*d+29) (node start (D 0) T)
      (node out (D 0) (recordWrite T (D 10+3*d+1) b0 b1 b2)) := by run_tac checkedFrom `FullBodyClosure.Stack "push_path"
private theorem pop_path : ∀ {D T P d out} (m : Fin 3) (b : Bool) (c : Fin 7),Grid D T → D 12 ≤ P → D 10+3*(d+1)+4 ≤ D 11 →
    (∀ j,j < d → ∃ a b c : Bool,(a && b && c)=false ∧ T (D 10+1+3*j)=some a ∧ T (D 10+1+3*j+1)=some b ∧ T (D 10+1+3*j+2)=some c) →
    T (D 10+3*d+1)=some (recordBit c 0) → T (D 10+3*d+2)=some (recordBit c 1) → T (D 10+3*d+3)=some (recordBit c 2) →
    T (D 10+3*(d+1)+1)=some true → T (D 10+3*(d+1)+2)=some true → T (D 10+3*(d+1)+3)=some true →
    PopRows m b out → Path P (2*(D 10-D 0)+6*d+36) (node (returnState m b) (D 0) T)
      (node (out c) (D 0) (recordWrite T (D 10+3*d+1) true true true)) := by run_tac checkedFrom `FullBodyClosure.Stack "pop_path"
private theorem push_actual (m : Fin 3) (c : Fin 7) :
    PushRows (pushState m c) (SerializedBodyCompletion.needEntry m) (recordBit c 0) (recordBit c 1) (recordBit c 2) := by
  fin_cases m <;> fin_cases c
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode0_0"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode0_1"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode0_2"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode0_3"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode0_4"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode0_5"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode0_6"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode1_0"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode1_1"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode1_2"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode1_3"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode1_4"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode1_5"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode1_6"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode2_0"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode2_1"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode2_2"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode2_3"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode2_4"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode2_5"
  · run_tac checkedFrom `FullBodyClosure.StackRows "pushCode2_6"
private theorem pop_actual (m : Fin 3) (b : Bool) : PopRows m b (popNextState m b) := by
  fin_cases m <;> cases b
  · run_tac checkedFrom `FullBodyClosure.StackRows "popCode0_0"
  · run_tac checkedFrom `FullBodyClosure.StackRows "popCode0_1"
  · run_tac checkedFrom `FullBodyClosure.StackRows "popCode1_0"
  · run_tac checkedFrom `FullBodyClosure.StackRows "popCode1_1"
  · run_tac checkedFrom `FullBodyClosure.StackRows "popCode2_0"
  · run_tac checkedFrom `FullBodyClosure.StackRows "popCode2_1"

private theorem grid_mono : ∀ {D T},Grid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by run_tac checkedKernel "Grid.mono"
/-- Every continuation code is installed by the actual same-table push path. -/
private theorem push_records {D T P r K} (m : Fin 3) (c : Fin 7) (grid : Grid D T) (room : D 12 ≤ P)
    (len10 : D 11=D 10+3*r+4) (space : K.length < r) (stack : StackCells D T r K) :
    ∃ t,t ≤ 128*(P+1) ∧ Path P t (node (pushState m c) (D 0) T)
      (node (SerializedBodyCompletion.needEntry m) (D 0)
        (recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2))) ∧
      StackCells D (recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2)) r (K++[c]) := by
  have free0:=stack K.length (by omega) 0 (by decide)
  have free1:=stack K.length (by omega) 1 (by decide)
  have free2:=stack K.length (by omega) 2 (by decide)
  rw [recordCell_free K K.length 0 le_rfl] at free0
  rw [recordCell_free K K.length 1 le_rfl] at free1
  rw [recordCell_free K K.length 2 le_rfl] at free2
  have p0 : D 10+1+3*K.length+0=D 10+3*K.length+1 := by omega
  have p1 : D 10+1+3*K.length+1=D 10+3*K.length+2 := by omega
  have p2 : D 10+1+3*K.length+2=D 10+3*K.length+3 := by omega
  rw [p0] at free0
  rw [p1] at free1
  rw [p2] at free2
  have path:=push_path grid room (d:=K.length) (by omega) (stack_busy stack (by omega)) free0 free1 free2 (push_actual m c)
  refine ⟨_,?_,path,stack_push_cells stack c⟩
  have upper : D 11 ≤ P := by
    exact le_trans (grid_mono grid 11 12 (by decide) (by decide)) room
  omega
private theorem pop_records {D T P r K} (m : Fin 3) (b : Bool) (c : Fin 7) (grid : Grid D T) (room : D 12 ≤ P)
    (len10 : D 11=D 10+3*r+4) (space : K.length+1 ≤ r) (stack : StackCells D T r (K++[c])) :
    ∃ t,t ≤ 128*(P+1) ∧ Path P t (node (returnState m b) (D 0) T)
      (node (popNextState m b c) (D 0) (recordWrite T (D 10+3*K.length+1) true true true)) ∧
      StackCells D (recordWrite T (D 10+3*K.length+1) true true true) r K := by
  have old0:=stack K.length (by omega) 0 (by decide)
  have old1:=stack K.length (by omega) 1 (by decide)
  have old2:=stack K.length (by omega) 2 (by decide)
  rw [recordCell_last] at old0 old1 old2
  have free0:=stack (K.length+1) space 0 (by decide)
  have free1:=stack (K.length+1) space 1 (by decide)
  have free2:=stack (K.length+1) space 2 (by decide)
  rw [recordCell_free (K++[c]) (K.length+1) 0 (by simp)] at free0
  rw [recordCell_free (K++[c]) (K.length+1) 1 (by simp)] at free1
  rw [recordCell_free (K++[c]) (K.length+1) 2 (by simp)] at free2
  have p0 : ∀ j,D 10+1+3*j+0=D 10+3*j+1 := by intro j;omega
  have p1 : ∀ j,D 10+1+3*j+1=D 10+3*j+2 := by intro j;omega
  have p2 : ∀ j,D 10+1+3*j+2=D 10+3*j+3 := by intro j;omega
  rw [p0] at old0 free0
  rw [p1] at old1 free1
  rw [p2] at old2 free2
  have busy:=stack_busy stack (by simpa using space)
  have path:=pop_path m b c grid room (d:=K.length) (by omega)
    (by intro j hj;exact busy j (by simp;omega)) old0 old1 old2 free0 free1 free2 (pop_actual m b)
  refine ⟨_,?_,path,stack_pop_cells c stack⟩
  have upper : D 11 ≤ P := by
    exact le_trans (grid_mono grid 11 12 (by decide) (by decide)) room
  omega

end FullBodyClosure
