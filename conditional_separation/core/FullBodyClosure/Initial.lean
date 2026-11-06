import FullBodyClosure.Operand
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
open Lean Elab Tactic in
private def checkedCase (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num `_private.SerializedBodyCompletion.Case 0) "SerializedBodyCompletion")
  let some ci:=env.find? name | throwError "Missing exact immutable declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == `SerializedBodyCompletion.Case do throwError "Wrong owner: {name}"
  logInfo m!"initial-adapter|{name}|{ci.type}"
  closeMainGoal `checkedCase (mkConst name (ci.levelParams.map Level.param))
private abbrev value : (F r n g W a v u rem quota j i : Nat) → Bool := by run_tac checkedCase "cellValue"
private theorem rise : ∀ F r n j,j < 12 → SerializedBody.delimiter F r n j < SerializedBody.delimiter F r n (j+1) := by run_tac checkedCase "d_rise"
private theorem mono : ∀ F r n a b,a ≤ b → b ≤ 12 → SerializedBody.delimiter F r n a ≤ SerializedBody.delimiter F r n b := by run_tac checkedCase "d_mono"
private theorem image_blank : ∀ T F r n g W a v u rem quota j,j ≤ 12 →
    SerializedBody.image T F r n g W a v u rem quota (SerializedBody.delimiter F r n j)=none := by run_tac checkedCase "image_blank"
private theorem image_value : ∀ T F r n g W a v u rem quota j i,j < 12 →
    SerializedBody.delimiter F r n j < i → i < SerializedBody.delimiter F r n (j+1) →
    SerializedBody.image T F r n g W a v u rem quota i=some (value F r n g W a v u rem quota j i) := by run_tac checkedCase "image_value"
private theorem image_outside : ∀ T F r n g W a v u rem quota i,i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i →
    SerializedBody.image T F r n g W a v u rem quota i=T i := by run_tac checkedCase "image_outside"
private theorem beta_occupied : ∀ {n L H} (T : Nat → Option Bool) (beta : Fin n → Bool),H=L+n+1 →
    (∀ j : Fin n,T (H-1-j.val)=some (beta j)) → ∀ i,L < i → i < H → ∃ b,T i=some b := by run_tac checkedCase "beta_occupied"
private theorem context_make : ∀ {D T S L H Q F r M W n source beta},
    S < L → L < H → H=L+n+1 → 0 < Q → H+Q < F → D 0=F+1 →
    (∀ j,j < 12 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) →
    (∀ j,j ≤ 12 → T (D j)=none) → (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) →
    D 5=D 4+r+1 → D 12=D 11+r+1 → W ≤ r → T S=none → T L=none → T H=none → T F=some false →
    (∀ i,S < i → i < L → ∃ b,T i=some b) → (∀ i,L < i → i < H → ∃ b,T i=some b) →
    (∀ j : Fin n,T (H-1-j.val)=some (beta j)) → (∀ i,H < i → i ≤ H+Q → T i=some true) →
    (∀ i,H+Q < i → i < F → T i=none) → (∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) →
    Context D T S L H Q F r M W n source beta := by run_tac checkedFrom `FullBodyClosure.Invariant "Context.mk"
/-- The original complete prepared image supplies the shared invariant internally.
The raw source T, including any consumed header holes, is preserved outside the arena. -/
private theorem image_context (T : Nat → Option Bool) (S L H Q F r M W n g a nodes used rem quota : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool) (sl : S < L) (width : H=L+n+1)
    (positive : 0 < Q) (arena : H+Q < F) (hw : W ≤ r)
    (src : ∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (eof : T S=none) (reg : ∀ i,S < i → i < L → T i=some false) (left : T L=none)
    (betaCells : ∀ j : Fin n,T (H-1-j.val)=some (beta j)) (right : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (fence : T F=some false) :
    Context (SerializedBody.delimiter F r n) (SerializedBody.image T F r n g W a nodes used rem quota)
      S L H Q F r M W n source beta := by
  let D:=SerializedBody.delimiter F r n
  let V:=SerializedBody.image T F r n g W a nodes used rem quota
  have lh : L < H := by omega
  have d0 : D 0=F+1 := rfl
  have below (i : Nat) (hi : i < D 0) : SerializedBody.image T F r n g W a nodes used rem quota i=T i:=image_outside T F r n g W a nodes used rem quota i (Or.inl hi)
  refine context_make sl lh width positive arena d0 (rise F r n) (mono F r n)
    (image_blank T F r n g W a nodes used rem quota) ?_ ?_ ?_ hw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j i hj lo hi
    exact ⟨_,image_value T F r n g W a nodes used rem quota j i hj lo hi⟩
  · change F+4*r+n+6=F+3*r+n+5+r+1;omega
  · change F+13*r+2*n+16=F+12*r+2*n+15+r+1;omega
  · rw [below S (by omega)];exact eof
  · rw [below L (by omega)];exact left
  · rw [below H (by omega)];exact right
  · rw [below F (by omega)];exact fence
  · intro i lo hi;rw [below i (by omega)];exact ⟨false,reg i lo hi⟩
  · intro i lo hi;rw [below i (by omega)];exact beta_occupied T beta width betaCells i lo hi
  · intro j;rw [below (H-1-j.val) (by omega)];exact betaCells j
  · intro i lo hi;rw [below i (by omega)];exact marks i lo hi
  · intro i lo hi;rw [below i (by omega)];exact gap i lo hi
  · intro i lo hi;rw [below i (by omega)];exact src i lo hi
private theorem image_index_fields (T : Nat → Option Bool) (F r n g W a nodes used rem quota : Nat) :
    let D:=SerializedBody.delimiter F r n
    let V:=SerializedBody.image T F r n g W a nodes used rem quota
    Unary D V 1 0 ∧ Unary D V 2 (bitLength n) ∧ Unary D V 8 0 ∧
      (∀ i,D 9 < i → i < D 10 → V i=some false) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro i lo hi
    rw [image_value T F r n g W a nodes used rem quota 1 i (by decide) lo hi]
    change some false=some (decide (i-SerializedBody.delimiter F r n 1 ≤ 0))
    have no : ¬i-SerializedBody.delimiter F r n 1 ≤ 0 := by omega
    simp only [no,decide_false]
  · intro i lo hi
    exact image_value T F r n g W a nodes used rem quota 2 i (by decide) lo hi
  · intro i lo hi
    rw [image_value T F r n g W a nodes used rem quota 8 i (by decide) lo hi]
    change some false=some (decide (i-SerializedBody.delimiter F r n 8 ≤ 0))
    have no : ¬i-SerializedBody.delimiter F r n 8 ≤ 0 := by omega
    simp only [no,decide_false]
  · intro i lo hi
    exact image_value T F r n g W a nodes used rem quota 9 i (by decide) lo hi
private theorem prepared_memory (T : Nat → Option Bool) (S M F r n g W : Nat)
    (_before : S < SerializedBody.delimiter F r n 0) :
    memory (SerializedBody.image T F r n g W (S-min M S) 0 0 W g)
      (SerializedBody.delimiter F r n) S M W 0=SerializedBody.prepared T S M F r n g W := by
  let D:=SerializedBody.delimiter F r n
  let V:=SerializedBody.image T F r n g W (S-min M S) 0 0 W g
  funext i
  change (if i=M+0 ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else
    if D 11 < i ∧ i < D 12 then _ else V i)=(if i=M ∧ i < S then none else V i)
  simp only [Nat.add_zero,Nat.sub_zero]
  by_cases hole : i=M ∧ i < S
  · simp only [if_pos hole]
  · simp only [if_neg hole]
    by_cases in4 : D 4 < i ∧ i < D 5
    · rw [if_pos in4]
      exact (image_value T F r n g W (S-min M S) 0 0 W g 4 i (by decide) in4.1 in4.2).symm
    · rw [if_neg in4]
      by_cases in11 : D 11 < i ∧ i < D 12
      · rw [if_pos in11]
        exact (image_value T F r n g W (S-min M S) 0 0 W g 11 i (by decide) in11.1 in11.2).symm
      · rw [if_neg in11]
end FullBodyClosure
