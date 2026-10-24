import FullBodyClosure.Initial
import FullBodyClosure.Continuation
import FullBodyClosure.NodeRows
import FullBodyClosure.Rows0
import FullBodyClosure.Rows1
import FullBodyClosure.Rows2
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
private abbrev StackCells : (Nat → Nat) → (Nat → Option Bool) → Nat → List (Fin 7) → Prop := by run_tac checkedFrom `FullBodyClosure.Continuation "StackCells"
private theorem image_context : ∀ (T : Nat → Option Bool) (S L H Q F r M W n g a nodes used rem quota : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool),S < L → H=L+n+1 → 0 < Q → H+Q < F → W ≤ r →
    (∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) → T S=none →
    (∀ i,S < i → i < L → T i=some false) → T L=none →
    (∀ j : Fin n,T (H-1-j.val)=some (beta j)) → T H=none →
    (∀ i,H < i → i ≤ H+Q → T i=some true) → (∀ i,H+Q < i → i < F → T i=none) → T F=some false →
    Context (SerializedBody.delimiter F r n) (SerializedBody.image T F r n g W a nodes used rem quota)
      S L H Q F r M W n source beta := by run_tac checkedFrom `FullBodyClosure.Initial "image_context"
private theorem image_index_fields : ∀ (T : Nat → Option Bool) (F r n g W a nodes used rem quota : Nat),
    let D:=SerializedBody.delimiter F r n
    let V:=SerializedBody.image T F r n g W a nodes used rem quota
    Unary D V 1 0 ∧ Unary D V 2 (bitLength n) ∧ Unary D V 8 0 ∧
      (∀ i,D 9 < i → i < D 10 → V i=some false) := by run_tac checkedFrom `FullBodyClosure.Initial "image_index_fields"
/-- ONE proof-only physical invariant for native Need/Return recurrence.
All numeric metadata in this proposition names real unary fields or addresses;
there is no parse-success/oracle-result/assumed execution field. -/
private structure Rep (base : Nat → Option Bool) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r M W n g u v : Nat) (source : Fin S → Bool) (beta : Fin n → Bool) (K : List (Fin 7)) : Prop where
  context : Context D T S L H Q F r M W n source beta
  outside : ∀ i,i < D 0 ∨ D 12 < i → T i=base i
  cap : g ≤ r
  cursor : u ≤ W
  seen : v ≤ g
  depth : K.length ≤ v
  ellBound : bitLength n ≤ r
  originalQuota : Unary D T 0 g
  index : Unary D T 1 0
  ell : Unary D T 2 (bitLength n)
  originalWindow : Unary D T 3 W
  nodes : Unary D T 5 v
  quota : Unary D T 6 (g-v)
  anchor : Unary D T 7 (S-min M S)
  j : Unary D T 8 0
  buffer : ∀ i,D 9 < i → i < D 10 → T i=some false
  stack : StackCells D T r K
private theorem initial_rep (T : Nat → Option Bool) (S L H Q F r M W n g : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool) (sl : S < L) (width : H=L+n+1)
    (positive : 0 < Q) (arena : H+Q < F) (hg : g ≤ r) (hw : W ≤ r) (he : bitLength n ≤ r)
    (src : ∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (eof : T S=none) (reg : ∀ i,S < i → i < L → T i=some false) (left : T L=none)
    (betaCells : ∀ j : Fin n,T (H-1-j.val)=some (beta j)) (right : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (fence : T F=some false) :
    Rep T (SerializedBody.delimiter F r n) (SerializedBody.image T F r n g W (S-min M S) 0 0 W g)
      S L H Q F r M W n g 0 0 source beta [] := by
  have ctx:=image_context T S L H Q F r M W n g (S-min M S) 0 0 W g source beta sl width positive arena hw
    src eof reg left betaCells right marks gap fence
  obtain ⟨u1,u2,u8,buf⟩:=image_index_fields T F r n g W (S-min M S) 0 0 W g
  refine ⟨ctx,image_outside T F r n g W (S-min M S) 0 0 W g,hg,by omega,by omega,by simp,he,
    ?_,u1,u2,?_,?_,?_,?_,u8,buf,?_⟩
  · intro i lo hi;exact image_value T F r n g W (S-min M S) 0 0 W g 0 i (by decide) lo hi
  · intro i lo hi;exact image_value T F r n g W (S-min M S) 0 0 W g 3 i (by decide) lo hi
  · intro i lo hi;exact image_value T F r n g W (S-min M S) 0 0 W g 5 i (by decide) lo hi
  · intro i lo hi;exact image_value T F r n g W (S-min M S) 0 0 W g 6 i (by decide) lo hi
  · intro i lo hi;exact image_value T F r n g W (S-min M S) 0 0 W g 7 i (by decide) lo hi
  · intro j hj b hb
    change SerializedBody.image T F r n g W (S-min M S) 0 0 W g
      (SerializedBody.delimiter F r n 10+1+3*j+b)=some true
    apply image_value T F r n g W (S-min M S) 0 0 W g 10 _ (by decide)
    · omega
    · change F+9*r+2*n+11+1+3*j+b < F+12*r+2*n+15
      omega

private theorem grid_mono : ∀ {D T},Grid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by
  run_tac checkedKernel "Grid.mono"
private theorem grid_blank : ∀ {D T},Grid D T → ∀ j,j ≤ 12 → T (D j)=none := by
  run_tac checkedKernel "Grid.blank"
private theorem grid_cells : ∀ {D T},Grid D T → ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b := by
  run_tac checkedKernel "Grid.cells"
private theorem Context.grid : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → Grid D T := by
  run_tac checkedFrom `FullBodyClosure.Invariant "Context.grid"
private theorem Context.before : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → S < D 0 := by
  run_tac checkedFrom `FullBodyClosure.Invariant "Context.before"
private theorem Context.withWorkspace : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ U,
    (∀ i,i < D 0 → U i=T i) → (∀ j,j ≤ 12 → U (D j)=none) →
    (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,U i=some b) →
    Context D U S L H Q F r M W n source beta := by
  run_tac checkedFrom `FullBodyClosure.Invariant "Context.withWorkspace"
private theorem Context.withCounter : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ j v,j < 12 →
    Context D (counter T D j v) S L H Q F r M W n source beta := by
  run_tac checkedFrom `FullBodyClosure.Invariant "Context.withCounter"
private theorem counter_unary : ∀ T D j v,Unary D (counter T D j v) j v := by
  run_tac checkedFrom `FullBodyClosure.Index "counter_unary"
private theorem counter_other : ∀ {D T j k v w},Grid D T → j < 12 → k < 12 → j≠k → Unary D T j v →
    Unary D (counter T D k w) j v := by run_tac checkedFrom `FullBodyClosure.Copy "counter_other"
private theorem outside_field {D : Nat → Nat}
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) {j k i : Nat}
    (hj : j < 12) (hk : k < 12) (ne : j≠k) (inside : D j < i ∧ i < D (j+1)) :
    ¬(D k < i ∧ i < D (k+1)) := by
  by_cases order : j < k
  · have :=mono (j+1) k (by omega) (by omega);omega
  · have :=mono (k+1) j (by omega) (by omega);omega
private theorem Rep.advance {base D T S L H Q F r M W n g u v source beta K}
    (rep : Rep base D T S L H Q F r M W n g u v source beta K) {u'} (cursor : u' ≤ W) :
    Rep base D T S L H Q F r M W n g u' v source beta K :=
  { rep with cursor:=cursor }
/-- Reframing of an ALREADY executed workspace update. No execution is inferred
from this lemma; callers must separately compose the literal native path. -/
private theorem Rep.reframe {base D T S L H Q F r M W n g u v source beta K}
    (rep : Rep base D T S L H Q F r M W n g u v source beta K)
    (U : Nat → Option Bool) (v' : Nat) (K' : List (Fin 7))
    (grid : Grid D U) (outside : ∀ i,i < D 0 ∨ D 12 < i → U i=T i)
    (fixed : ∀ j,j < 12 → j≠5 → j≠6 → j≠10 → ∀ i,D j < i → i < D (j+1) → U i=T i)
    (nodes : Unary D U 5 v') (quota : Unary D U 6 (g-v'))
    (seen : v' ≤ g) (depth : K'.length ≤ v') (stack : StackCells D U r K') :
    Rep base D U S L H Q F r M W n g u v' source beta K' := by
  have ctx:=rep.context.withWorkspace U (by intro i hi;exact outside i (Or.inl hi)) (grid_blank grid) (grid_cells grid)
  have lift (j v : Nat) (hj : j < 12) (h5 : j≠5) (h6 : j≠6) (h10 : j≠10)
      (h : Unary D T j v) : Unary D U j v := by
    intro i lo hi
    rw [fixed j hj h5 h6 h10 i lo hi]
    exact h i lo hi
  refine ⟨ctx,?_,rep.cap,rep.cursor,seen,depth,rep.ellBound,
    lift 0 g (by decide) (by decide) (by decide) (by decide) rep.originalQuota,
    lift 1 0 (by decide) (by decide) (by decide) (by decide) rep.index,
    lift 2 (bitLength n) (by decide) (by decide) (by decide) (by decide) rep.ell,
    lift 3 W (by decide) (by decide) (by decide) (by decide) rep.originalWindow,nodes,quota,
    lift 7 (S-min M S) (by decide) (by decide) (by decide) (by decide) rep.anchor,
    lift 8 0 (by decide) (by decide) (by decide) (by decide) rep.j,?_,stack⟩
  · intro i hi;rw [outside i hi];exact rep.outside i hi
  · intro i lo hi;rw [fixed 9 (by decide) (by decide) (by decide) (by decide) i lo hi]
    exact rep.buffer i lo hi
private theorem Rep.opened {base D T S L H Q F r M W n g u v source beta K}
    (rep : Rep base D T S L H Q F r M W n g u v source beta K) (paid : v < g)
    (len10 : D 11=D 10+3*r+4) :
    Rep base D (counter (counter T D 6 (g-(v+1))) D 5 (v+1))
      S L H Q F r M W n g u (v+1) source beta K := by
  let A:=counter T D 6 (g-(v+1))
  let U:=counter A D 5 (v+1)
  have ca:=rep.context.withCounter 6 (g-(v+1)) (by decide)
  have cu:=ca.withCounter 5 (v+1) (by decide)
  have ma:=rep.context
  have same (i : Nat) (h5 : ¬(D 5 < i ∧ i < D 6)) (h6 : ¬(D 6 < i ∧ i < D 7)) : U i=T i := by
    change (if D 5 < i ∧ i < D 6 then _ else if D 6 < i ∧ i < D 7 then _ else T i)=T i
    rw [if_neg h5,if_neg h6]
  have outside (i : Nat) (hi : i < D 0 ∨ D 12 < i) : U i=T i := by
    have :=(grid_mono ma.grid) 0 5 (by decide) (by decide)
    have :=(grid_mono ma.grid) 0 6 (by decide) (by decide)
    have :=(grid_mono ma.grid) 6 12 (by decide) (by decide)
    have :=(grid_mono ma.grid) 7 12 (by decide) (by decide)
    exact same i (by omega) (by omega)
  have fixed (j : Nat) (hj : j < 12) (h5 : j≠5) (h6 : j≠6) (_h10 : j≠10)
      (i : Nat) (lo : D j < i) (hi : i < D (j+1)) : U i=T i :=
    same i (outside_field (grid_mono ma.grid) hj (by decide) h5 ⟨lo,hi⟩)
      (outside_field (grid_mono ma.grid) hj (by decide) h6 ⟨lo,hi⟩)
  apply rep.reframe U (v+1) K cu.grid outside fixed (counter_unary A D 5 (v+1))
    (counter_other ca.grid (by decide) (by decide) (by decide) (counter_unary T D 6 (g-(v+1))))
    (by omega) (by have :=rep.depth;omega)
  intro j hj b hb
  have lo : D 10 < D 10+1+3*j+b := by omega
  have hi : D 10+1+3*j+b < D 11 := by
    omega
  rw [same _ (outside_field (grid_mono ma.grid) (by decide) (by decide) (by decide) ⟨lo,hi⟩)
    (outside_field (grid_mono ma.grid) (by decide) (by decide) (by decide) ⟨lo,hi⟩)]
  exact rep.stack j hj b hb
private abbrev put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by
  run_tac checkedKernel "put"
private theorem counter_down : ∀ T D j v w,D (j+1)=D j+w+1 → 0 < v → v ≤ w →
    put (counter T D j v) (D j+v) (some false)=counter T D j (v-1) := by
  run_tac checkedFrom `FullBodyClosure.Index "counter_down"
private theorem counter_up : ∀ T D j v w,D (j+1)=D j+w+1 → v < w →
    put (counter T D j v) (D j+v+1) (some true)=counter T D j (v+1) := by
  run_tac checkedFrom `FullBodyClosure.Index "counter_up"
private theorem memory_grid : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ u,Grid D (memory T D S M W u) := by
  run_tac checkedFrom `FullBodyClosure.Input "memory_grid"
private theorem memory_counter : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ u j v,j < 12 → j≠4 → j≠11 →
    counter (memory T D S M W u) D j v=memory (counter T D j v) D S M W u := by
  run_tac checkedFrom `FullBodyClosure.Input "memory_counter"
private theorem memory_unary : ∀ {D T S L H Q F r M W n source beta j v},
    Context D T S L H Q F r M W n source beta → ∀ u,j < 12 → j≠4 → j≠11 → Unary D T j v →
    Unary D (memory T D S M W u) j v := by run_tac checkedFrom `FullBodyClosure.Input "memory_unary"
private theorem grid_rise : ∀ {D T},Grid D T → ∀ j,j < 12 → D j < D (j+1) := by
  run_tac checkedKernel "Grid.rise"
private theorem counter_fixed {D T j v} (unary : Unary D T j v) : counter T D j v=T := by
  funext i
  change (if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else T i)=T i
  split_ifs with h
  · exact (unary i h.1 h.2).symm
  · rfl
private theorem need_update {D T r q v} (grid : Grid D T)
    (len5 : D 6=D 5+r+1) (len6 : D 7=D 6+r+1) (paid : 0 < q) (bound : q+v ≤ r)
    (quota : Unary D T 6 q) (nodes : Unary D T 5 v) :
    (fun i=>if i=D 5+v+1 then some true else if i=D 6+q then some false else T i)=
      counter (counter T D 6 (q-1)) D 5 (v+1) := by
  have down : put T (D 6+q) (some false)=counter T D 6 (q-1) := by
    have h:=counter_down T D 6 q r len6 paid (by omega)
    rw [counter_fixed quota] at h;exact h
  have nodes' : Unary D (counter T D 6 (q-1)) 5 v :=
    counter_other grid (by decide) (by decide) (by decide) nodes
  have up : put (counter T D 6 (q-1)) (D 5+v+1) (some true)=
      counter (counter T D 6 (q-1)) D 5 (v+1) := by
    have h:=counter_up (counter T D 6 (q-1)) D 5 v r len5 (by omega)
    rw [counter_fixed nodes'] at h;exact h
  change put (put T (D 6+q) (some false)) (D 5+v+1) (some true)=_
  rw [down,up]
/-- One native opener on the shared representation. The counter edits commute
with the CURRENT physical source hole; they do not install a fresh source. -/
private theorem Rep.need {base D T S L H Q F r M W n g u v source beta K}
    (rep : Rep base D T S L H Q F r M W n g u v source beta K)
    (paid : v < g) (len5 : D 6=D 5+r+1) (len6 : D 7=D 6+r+1) (len10 : D 11=D 10+3*r+4)
    (N B P : Nat) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let U:=counter (counter T D 6 (g-(v+1))) D 5 (v+1)
    ∃ t,t ≤ 128*(P+1) ∧
      Native t
        (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
          fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
        (⟨SerializedBodyRefinement.getEntry 0 (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
          fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
      Rep base D U S L H Q F r M W n g u (v+1) source beta K := by
  let mode:=SerializedBody.sourceMode source (M+u)
  let V:=memory T D S M W u
  have grid:=memory_grid rep.context u
  obtain ⟨price,run,prefixBound⟩:=SerializedBodyCompletion.need_get mode D V r (g-v) v N B P
    (grid_rise grid) (grid_mono grid) (grid_blank grid) (grid_cells grid) room fit h0
    (by omega) (by have :=rep.seen;have :=rep.cap;omega) len5 len6
    (memory_unary rep.context u (by decide) (by decide) (by decide) rep.quota)
    (memory_unary rep.context u (by decide) (by decide) (by decide) rep.nodes)
  have updated:=need_update grid len5 len6 (by omega : 0 < g-v)
    (by have :=rep.seen;have :=rep.cap;omega)
    (memory_unary rep.context u (by decide) (by decide) (by decide) rep.quota)
    (memory_unary rep.context u (by decide) (by decide) (by decide) rep.nodes)
  have sub : g-v-1=g-(v+1) := by omega
  rw [sub,memory_counter rep.context u 6 (g-(v+1)) (by decide) (by decide) (by decide),
    memory_counter (rep.context.withCounter 6 (g-(v+1)) (by decide)) u 5 (v+1) (by decide) (by decide) (by decide)] at updated
  have eq:=congrArg (fun f : Nat → Option Bool=>fun i : Fin (tapeLength N B)=>f i.val) updated
  change (fun i : Fin (tapeLength N B)=>if i.val=D 5+v+1 then some true else if i.val=D 6+(g-v) then some false else V i.val)=_ at eq
  rw [eq] at run
  refine ⟨_,price,⟨run,?_⟩,rep.opened paid len10⟩
  intro j hj;exact prefixBound j (by omega)

private abbrev recordBit : Fin 7 → Nat → Bool := by run_tac checkedFrom `FullBodyClosure.Representation "recordBit"
private abbrev recordWrite : (Nat → Option Bool) → Nat → Bool → Bool → Bool → Nat → Option Bool := by
  run_tac checkedFrom `FullBodyClosure.Continuation "recordWrite"
private theorem recordWrite_outside : ∀ T a i b0 b1 b2,i < a ∨ a+3 ≤ i →
    recordWrite T a b0 b1 b2 i=T i := by run_tac checkedFrom `FullBodyClosure.Continuation "recordWrite_outside"
private theorem grid_make : ∀ {D T},(∀ j,j < 12 → D j < D (j+1)) →
    (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) → (∀ j,j ≤ 12 → T (D j)=none) →
    (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) → Grid D T := by
  run_tac checkedKernel "Grid.mk"
private theorem recordWrite_grid {D T a} (grid : Grid D T) (lo : D 10 < a) (hi : a+2 < D 11)
    (b0 b1 b2 : Bool) : Grid D (recordWrite T a b0 b1 b2) := by
  have mono:=grid_mono grid
  have out (j : Nat) (hj : j ≤ 12) : D j < a ∨ a+3 ≤ D j := by
    by_cases early : j ≤ 10
    · have :=mono j 10 early (by decide);omega
    · have :=mono 11 j (by omega) hj;omega
  apply grid_make (grid_rise grid) mono
  · intro j hj;rw [recordWrite_outside T a _ b0 b1 b2 (out j hj)];exact grid_blank grid j hj
  · intro j i hj il ih
    change ∃ b,(if i=a then some b0 else if i=a+1 then some b1 else if i=a+2 then some b2 else T i)=some b
    split_ifs
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact ⟨_,rfl⟩
    · exact grid_cells grid j i hj il ih
private theorem Rep.records {base D T S L H Q F r M W n g u v source beta K}
    (rep : Rep base D T S L H Q F r M W n g u v source beta K)
    (a : Nat) (b0 b1 b2 : Bool) (K' : List (Fin 7))
    (lo : D 10 < a) (hi : a+2 < D 11) (depth : K'.length ≤ v)
    (stack : StackCells D (recordWrite T a b0 b1 b2) r K') :
    Rep base D (recordWrite T a b0 b1 b2) S L H Q F r M W n g u v source beta K' := by
  have grid:=rep.context.grid
  have mono:=grid_mono grid
  have fixed (j : Nat) (hj : j < 12) (ne : j≠10) (i : Nat) (il : D j < i) (ih : i < D (j+1)) :
      recordWrite T a b0 b1 b2 i=T i := by
    have apart:=outside_field mono hj (by decide) ne ⟨il,ih⟩
    change ¬(D 10 < i ∧ i < D 11) at apart
    exact recordWrite_outside T a i b0 b1 b2 (by omega)
  apply rep.reframe _ v K' (recordWrite_grid grid lo hi b0 b1 b2)
  · intro i outside
    have :=mono 0 10 (by decide) (by decide)
    have :=mono 11 12 (by decide) (by decide)
    exact recordWrite_outside T a i b0 b1 b2 (by omega)
  · intro j hj _h5 _h6 h10 i il ih;exact fixed j hj h10 i il ih
  · intro i il ih;rw [fixed 5 (by decide) (by decide) i il ih];exact rep.nodes i il ih
  · intro i il ih;rw [fixed 6 (by decide) (by decide) i il ih];exact rep.quota i il ih
  · exact rep.seen
  · exact depth
  · exact stack
private theorem memory_field {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u j i : Nat)
    (hj : j < 12) (ne4 : j≠4) (ne11 : j≠11) (lo : D j < i) (hi : i < D (j+1)) :
    memory T D S M W u i=T i := by
  have mono:=grid_mono ctx.grid
  have before:=ctx.before
  have :=mono 0 j (by omega) (by omega)
  change (if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else
    if D 11 < i ∧ i < D 12 then _ else T i)=T i
  rw [if_neg (by omega : ¬(i=M+u ∧ i < S)),
    if_neg (outside_field mono hj (by decide) ne4 ⟨lo,hi⟩),
    if_neg (outside_field mono hj (by decide) ne11 ⟨lo,hi⟩)]
private theorem memory_records {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u a : Nat)
    (lo : D 10 < a) (hi : a+2 < D 11) (b0 b1 b2 : Bool) :
    recordWrite (memory T D S M W u) a b0 b1 b2=memory (recordWrite T a b0 b1 b2) D S M W u := by
  have mono:=grid_mono ctx.grid
  have before:=ctx.before
  have lower:=mono 0 10 (by decide) (by decide)
  have sep4:=mono 5 10 (by decide) (by decide)
  funext i
  by_cases at0 : i=a
  · subst i
    change (if a=a then some b0 else _)=_
    rw [if_pos rfl]
    change some b0=(if a=M+u ∧ a < S then none else if D 4 < a ∧ a < D 5 then _ else
      if D 11 < a ∧ a < D 12 then _ else if a=a then some b0 else _)
    rw [if_neg (by omega : ¬(a=M+u ∧ a < S)),if_neg (by omega : ¬(D 4 < a ∧ a < D 5)),
      if_neg (by omega : ¬(D 11 < a ∧ a < D 12)),if_pos rfl]
  by_cases at1 : i=a+1
  · subst i
    change (if a+1=a then _ else if a+1=a+1 then some b1 else _)=_
    rw [if_neg (by omega : a+1≠a),if_pos rfl]
    change some b1=(if a+1=M+u ∧ a+1 < S then none else if D 4 < a+1 ∧ a+1 < D 5 then _ else
      if D 11 < a+1 ∧ a+1 < D 12 then _ else if a+1=a then _ else if a+1=a+1 then some b1 else _)
    rw [if_neg (by omega : ¬(a+1=M+u ∧ a+1 < S)),if_neg (by omega : ¬(D 4 < a+1 ∧ a+1 < D 5)),
      if_neg (by omega : ¬(D 11 < a+1 ∧ a+1 < D 12)),if_neg (by omega : a+1≠a),if_pos rfl]
  by_cases at2 : i=a+2
  · subst i
    change (if a+2=a then _ else if a+2=a+1 then _ else if a+2=a+2 then some b2 else _)=_
    rw [if_neg (by omega : a+2≠a),if_neg (by omega : a+2≠a+1),if_pos rfl]
    change some b2=(if a+2=M+u ∧ a+2 < S then none else if D 4 < a+2 ∧ a+2 < D 5 then _ else
      if D 11 < a+2 ∧ a+2 < D 12 then _ else if a+2=a then _ else if a+2=a+1 then _ else if a+2=a+2 then some b2 else _)
    rw [if_neg (by omega : ¬(a+2=M+u ∧ a+2 < S)),if_neg (by omega : ¬(D 4 < a+2 ∧ a+2 < D 5)),
      if_neg (by omega : ¬(D 11 < a+2 ∧ a+2 < D 12)),if_neg (by omega : a+2≠a),if_neg (by omega : a+2≠a+1),if_pos rfl]
  have outside : i < a ∨ a+3 ≤ i := by omega
  rw [recordWrite_outside _ a i b0 b1 b2 outside]
  change memory T D S M W u i=(if i=M+u ∧ i < S then none else
    if D 4 < i ∧ i < D 5 then _ else if D 11 < i ∧ i < D 12 then _ else recordWrite T a b0 b1 b2 i)
  rw [recordWrite_outside T a i b0 b1 b2 outside]
  rfl
private abbrev pushState : Fin 3 → Fin 7 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.StackRows "pushState"
private abbrev popNextState : Fin 3 → Bool → Fin 7 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.StackRows "popNextState"
private theorem push_records : ∀ {D T P r K} (m : Fin 3) (c : Fin 7),Grid D T → D 12 ≤ P →
    D 11=D 10+3*r+4 → K.length < r → StackCells D T r K →
    ∃ t,t ≤ 128*(P+1) ∧ Path P t (node (pushState m c) (D 0) T)
      (node (SerializedBodyCompletion.needEntry m) (D 0)
        (recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2))) ∧
      StackCells D (recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2)) r (K++[c]) := by
  run_tac checkedFrom `FullBodyClosure.Continuation "push_records"
private theorem pop_records : ∀ {D T P r K} (m : Fin 3) (b : Bool) (c : Fin 7),Grid D T → D 12 ≤ P →
    D 11=D 10+3*r+4 → K.length+1 ≤ r → StackCells D T r (K++[c]) →
    ∃ t,t ≤ 128*(P+1) ∧ Path P t (node (returnState m b) (D 0) T)
      (node (popNextState m b c) (D 0) (recordWrite T (D 10+3*K.length+1) true true true)) ∧
      StackCells D (recordWrite T (D 10+3*K.length+1) true true true) r K := by
  run_tac checkedFrom `FullBodyClosure.Continuation "pop_records"
private theorem memory_stack {D T S L H Q F r M W n source beta K}
    (ctx : Context D T S L H Q F r M W n source beta) (u : Nat)
    (len10 : D 11=D 10+3*r+4) (stack : StackCells D T r K) :
    StackCells D (memory T D S M W u) r K := by
  intro j hj b hb
  rw [memory_field ctx u 10 _ (by decide) (by decide) (by decide) (by omega) (by change _ < D 11;omega)]
  exact stack j hj b hb
private theorem stack_push_cells : ∀ {D T r K},StackCells D T r K → ∀ c : Fin 7,
    StackCells D (recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2)) r (K++[c]) := by
  run_tac checkedFrom `FullBodyClosure.Continuation "stack_push_cells"
private theorem stack_pop_cells : ∀ {D T r K} (c : Fin 7),StackCells D T r (K++[c]) →
    StackCells D (recordWrite T (D 10+3*K.length+1) true true true) r K := by
  run_tac checkedFrom `FullBodyClosure.Continuation "stack_pop_cells"
private theorem Rep.push {base D T S L H Q F r M W n g u v source beta K}
    (rep : Rep base D T S L H Q F r M W n g u v source beta K)
    (c : Fin 7) (depth : K.length+1 ≤ v) (len10 : D 11=D 10+3*r+4)
    (N B P : Nat) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let U:=recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2)
    ∃ t,t ≤ 128*(P+1) ∧ Native t
      (⟨pushState (SerializedBody.sourceMode source (M+u)) c,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
      Rep base D U S L H Q F r M W n g u v source beta (K++[c]) := by
  have space : K.length < r := by have :=rep.seen;have :=rep.cap;omega
  have lo : D 10 < D 10+3*K.length+1 := by omega
  have hi : D 10+3*K.length+1+2 < D 11 := by omega
  obtain ⟨t,price,path,_stack⟩:=push_records (SerializedBody.sourceMode source (M+u)) c
    (memory_grid rep.context u) room len10 space (memory_stack rep.context u len10 rep.stack)
  have eq:=memory_records rep.context u _ lo hi (recordBit c 0) (recordBit c 1) (recordBit c 2)
  rw [eq] at path
  refine ⟨t,price,⟨path.execute fit,path.prefix fit⟩,?_⟩
  exact rep.records _ _ _ _ (K++[c]) lo hi (by simpa only [List.length_append,List.length_singleton] using depth)
    (stack_push_cells rep.stack c)
private theorem Rep.pop {base D T S L H Q F r M W n g u v source beta K}
    (c : Fin 7) (rep : Rep base D T S L H Q F r M W n g u v source beta (K++[c]))
    (b : Bool) (len10 : D 11=D 10+3*r+4)
    (N B P : Nat) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let U:=recordWrite T (D 10+3*K.length+1) true true true
    ∃ t,t ≤ 128*(P+1) ∧ Native t
      (⟨returnState (SerializedBody.sourceMode source (M+u)) b,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (⟨popNextState (SerializedBody.sourceMode source (M+u)) b c,⟨D 0,h0⟩,
        fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
      Rep base D U S L H Q F r M W n g u v source beta K := by
  have depth : K.length+1 ≤ v := by
    have h:=rep.depth
    simpa only [List.length_append,List.length_singleton] using h
  have space : K.length+1 ≤ r := by have :=rep.seen;have :=rep.cap;omega
  have lo : D 10 < D 10+3*K.length+1 := by omega
  have hi : D 10+3*K.length+1+2 < D 11 := by omega
  obtain ⟨t,price,path,_stack⟩:=pop_records (SerializedBody.sourceMode source (M+u)) b c
    (memory_grid rep.context u) room len10 space (memory_stack rep.context u len10 rep.stack)
  have eq:=memory_records rep.context u _ lo hi true true true
  rw [eq] at path
  refine ⟨t,price,⟨path.execute fit,path.prefix fit⟩,?_⟩
  exact rep.records _ true true true K lo hi (by omega) (stack_pop_cells c rep.stack)
private abbrev second : Bool → Fin 9 := by run_tac checkedFrom `FullBodyClosure.NodeRows "second"
private abbrev third : Bool → Bool → Fin 9 := by run_tac checkedFrom `FullBodyClosure.NodeRows "third"
private abbrev constState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Control "constState"
private abbrev tagDestination : Fin 3 → Bool → Bool → Bool → Fin 7500 := by
  run_tac checkedFrom `FullBodyClosure.Control "tagDestination"
private theorem first_row : ∀ b m,SerializedBody.machine.step (SerializedBodyRefinement.getExit 0 b m) none=
    (SerializedBodyRefinement.getEntry (second b) m,none,.stay) := by run_tac checkedFrom `FullBodyClosure.NodeRows "first_row"
private theorem second_row : ∀ a b m,SerializedBody.machine.step (SerializedBodyRefinement.getExit (second a) b m) none=
    (SerializedBodyRefinement.getEntry (third a b) m,none,.stay) := by run_tac checkedFrom `FullBodyClosure.NodeRows "second_row"
private theorem tag_exit : ∀ m a b c,SerializedBodyRefinement.getExit (third a b) c m=tagDestination m a b c := by
  run_tac checkedFrom `FullBodyClosure.Control "tag_exit"
private theorem get_exit_safe : ∀ s b m,4 ≤ (SerializedBodyRefinement.getExit s b m).val := by
  run_tac checkedFrom `FullBodyClosure.NodeRows "get_exit_safe"
private theorem read_plain : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ u N B P (site : Fin 9),u < W →
    D 12 ≤ P → P < tapeLength N B → ∀ h0 : D 0 < tapeLength N B,
    ∃ t,t ≤ 64*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getEntry site (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyRefinement.getExit site (padRead source (M+u)) (SerializedBody.sourceMode source (M+(u+1))),⟨D 0,h0⟩,
        fun i=>memory T D S M W (u+1) i.val⟩ : Config 7500 N B) := by
  run_tac checkedFrom `FullBodyClosure.Input "read_plain"
private theorem empty_get : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ N B P (site : Fin 9) (m : Fin 3),
    D 12 ≤ P → P < tapeLength N B → ∀ h0 : D 0 < tapeLength N B,
    ∃ t,t ≤ 64*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getEntry site m,⟨D 0,h0⟩,fun i=>memory T D S M W W i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyRefinement.getAbort m,⟨D 0,h0⟩,fun i=>memory T D S M W W i.val⟩ : Config 7500 N B) := by
  run_tac checkedFrom `FullBodyClosure.Input "empty_get"
private theorem native_stay {N B : Nat} (s q : Fin 7500) (T : Nat → Option Bool)
    (h : Fin (tapeLength N B)) (blank : T h.val=none) (safe : 4 ≤ s.val)
    (row : SerializedBody.machine.step s none=(q,none,.stay)) :
    Native 1 (⟨s,h,fun i=>T i.val⟩ : Config 7500 N B) ⟨q,h,fun i=>T i.val⟩ := by
  constructor
  · change SerializedBody.machine.stepConfig _=_
    apply Config.ext_parts
    · change (SerializedBody.machine.step s (T h.val)).1=q
      rw [blank,row]
    · apply Fin.ext
      change (moveHead h (SerializedBody.machine.step s (T h.val)).2.2).val=h.val
      rw [blank,row];rfl
    · funext i
      change (if i=h then (SerializedBody.machine.step s (T h.val)).2.1 else T i.val)=T i.val
      rw [blank,row]
      by_cases eq : i=h
      · subst i;simp only [↓reduceIte,blank]
      · simp only [if_neg eq]
  · intro j hj
    have eq : j=0 := by omega
    subst j;exact safe
/-- Every tag case, including logical lengths zero, one and two. The latter
execute their positive reads and dispatch stays before the exhausted Get. -/
private theorem tag_total {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u N B P : Nat)
    (cursor : u ≤ W) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 256*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getEntry 0 (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (if u+3 ≤ W then
        ⟨tagDestination (SerializedBody.sourceMode source (M+(u+3)))
          (padRead source (M+u)) (padRead source (M+(u+1))) (padRead source (M+(u+2))),⟨D 0,h0⟩,
          fun i=>memory T D S M W (u+3) i.val⟩
       else ⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+W)),⟨D 0,h0⟩,
          fun i=>memory T D S M W W i.val⟩ : Config 7500 N B) := by
  have blank (v : Nat) : memory T D S M W v (D 0)=none := grid_blank (memory_grid ctx v) 0 (by decide)
  by_cases end0 : u=W
  · subst u
    obtain ⟨t,price,run⟩:=empty_get ctx N B P 0 (SerializedBody.sourceMode source (M+W)) room fit h0
    refine ⟨t,by omega,?_⟩
    simpa only [show ¬W+3 ≤ W by omega,↓reduceIte] using run
  have hread0 : u < W := by omega
  obtain ⟨t0,p0,r0⟩:=read_plain ctx u N B P 0 hread0 room fit h0
  let b0:=padRead source (M+u)
  have one:=native_stay (SerializedBodyRefinement.getExit 0 b0 (SerializedBody.sourceMode source (M+(u+1))))
    (SerializedBodyRefinement.getEntry (second b0) (SerializedBody.sourceMode source (M+(u+1))))
    (memory T D S M W (u+1)) ⟨D 0,h0⟩ (blank _) (get_exit_safe _ _ _) (first_row _ _)
  have first:=native_trans r0 one
  by_cases end1 : u+1=W
  · rw [end1] at first
    obtain ⟨t,price,run⟩:=empty_get ctx N B P (second b0) (SerializedBody.sourceMode source (M+W)) room fit h0
    refine ⟨t0+1+t,by omega,?_⟩
    simpa only [show ¬u+3 ≤ W by omega,↓reduceIte] using native_trans first run
  have hread1 : u+1 < W := by omega
  obtain ⟨t1,p1,r1⟩:=read_plain ctx (u+1) N B P (second b0) hread1 room fit h0
  have sum2 : u+1+1=u+2 := by omega
  rw [sum2] at r1
  let b1:=padRead source (M+(u+1))
  have two:=native_stay (SerializedBodyRefinement.getExit (second b0) b1 (SerializedBody.sourceMode source (M+(u+2))))
    (SerializedBodyRefinement.getEntry (third b0 b1) (SerializedBody.sourceMode source (M+(u+2))))
    (memory T D S M W (u+2)) ⟨D 0,h0⟩ (blank _) (get_exit_safe _ _ _) (second_row _ _ _)
  have secondNative:=native_trans (native_trans first r1) two
  by_cases end2 : u+2=W
  · rw [end2] at secondNative
    obtain ⟨t,price,run⟩:=empty_get ctx N B P (third b0 b1) (SerializedBody.sourceMode source (M+W)) room fit h0
    refine ⟨t0+1+t1+1+t,by omega,?_⟩
    simpa only [show ¬u+3 ≤ W by omega,↓reduceIte] using native_trans secondNative run
  have hread2 : u+2 < W := by omega
  obtain ⟨t2,p2,r2⟩:=read_plain ctx (u+2) N B P (third b0 b1) hread2 room fit h0
  have sum3 : u+2+1=u+3 := by omega
  rw [sum3,tag_exit] at r2
  refine ⟨t0+1+t1+1+t2,by omega,?_⟩
  simpa only [show u+3 ≤ W by omega,↓reduceIte] using native_trans secondNative r2
/-- Failure frame: arbitrary DIRTY operands and continuation records are allowed.
Only the physical source/beta, immutable operands and complete exterior persist. -/
private structure AbortFrame (base : Nat → Option Bool) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r M W n g u : Nat) (source : Fin S → Bool) (beta : Fin n → Bool) : Prop where
  context : Context D T S L H Q F r M W n source beta
  outside : ∀ i,i < D 0 ∨ D 12 < i → T i=base i
  cursor : u ≤ W
  originalQuota : Unary D T 0 g
  ell : Unary D T 2 (bitLength n)
  originalWindow : Unary D T 3 W
  anchor : Unary D T 7 (S-min M S)
private theorem Rep.abortFrame {base D T S L H Q F r M W n g u v source beta K}
    (rep : Rep base D T S L H Q F r M W n g u v source beta K) :
    AbortFrame base D T S L H Q F r M W n g u source beta :=
  ⟨rep.context,rep.outside,rep.cursor,rep.originalQuota,rep.ell,rep.originalWindow,rep.anchor⟩
private theorem AbortFrame.advance {base D T S L H Q F r M W n g u source beta}
    (rep : AbortFrame base D T S L H Q F r M W n g u source beta) {u'} (cursor : u' ≤ W) :
    AbortFrame base D T S L H Q F r M W n g u' source beta := { rep with cursor:=cursor }
private theorem AbortFrame.withCounter {base D T S L H Q F r M W n g u source beta}
    (rep : AbortFrame base D T S L H Q F r M W n g u source beta)
    (j w : Nat) (hj : j < 12) (ne0 : j≠0) (ne2 : j≠2) (ne3 : j≠3) (ne7 : j≠7) :
    AbortFrame base D (counter T D j w) S L H Q F r M W n g u source beta := by
  have grid:=rep.context.grid
  have mono:=grid_mono grid
  refine ⟨rep.context.withCounter j w hj,?_,rep.cursor,
    counter_other grid (by decide) hj (Ne.symm ne0) rep.originalQuota,
    counter_other grid (by decide) hj (Ne.symm ne2) rep.ell,
    counter_other grid (by decide) hj (Ne.symm ne3) rep.originalWindow,
    counter_other grid (by decide) hj (Ne.symm ne7) rep.anchor⟩
  intro i outside
  have :=mono 0 j (by omega) (by omega)
  have :=mono (j+1) 12 (by omega) (by decide)
  change (if D j < i ∧ i < D (j+1) then _ else T i)=base i
  rw [if_neg (by omega : ¬(D j < i ∧ i < D (j+1)))]
  exact rep.outside i outside
private abbrev restored : {S : Nat} → (Nat → Option Bool) → (Nat → Nat) → (Fin S → Bool) → Nat → Nat → Option Bool := by
  run_tac checkedCase "restored"
private theorem restored_image : ∀ (base T : Nat → Option Bool) (S F r n g W a c : Nat) (source : Fin S → Bool),
    S < SerializedBody.delimiter F r n 0 → (c < S → base c=some (padRead source c)) →
    (∀ i,i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i → T i=(if c < S ∧ i=c then none else base i)) →
    (∀ j,j ≤ 12 → T (SerializedBody.delimiter F r n j)=none) →
    (∀ j,j∈[0,2,3,7] → ∀ i,SerializedBody.delimiter F r n j < i → i < SerializedBody.delimiter F r n (j+1) →
      T i=some (value F r n g W a 0 0 0 0 j i)) →
    restored T (SerializedBody.delimiter F r n) source c=SerializedBody.image base F r n g W a 0 0 0 0 := by
  run_tac checkedCase "restored_image"
private theorem memory_below : ∀ {T D S M W u i},(∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) → i < D 0 →
    memory T D S M W u i=(if i=M+u ∧ i < S then none else T i) := by
  run_tac checkedFrom `FullBodyClosure.Representation "memory_below"
private theorem AbortFrame.restored_eq {base T S L H Q F r M W n g u source beta}
    (rep : AbortFrame base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u source beta) :
    restored (memory T (SerializedBody.delimiter F r n) S M W u) (SerializedBody.delimiter F r n) source (M+u)=
      SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 := by
  let D:=SerializedBody.delimiter F r n
  have grid:=rep.context.grid
  have mono:=grid_mono grid
  change ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b at mono
  have before:=rep.context.before
  change S < D 0 at before
  apply restored_image base _ S F r n g W (S-min M S) (M+u) source before
  · intro physical
    have eq:=rep.outside (M+u) (Or.inl (by change M+u < D 0;omega))
    rcases rep.context with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
    rw [←eq,src _ (by omega) physical]
    simp only [padRead,physical,↓reduceDIte]
  · intro i outside
    change i < D 0 ∨ D 12 < i at outside
    by_cases low : i < D 0
    · rw [memory_below mono low,rep.outside i outside]
      have cond : (i=M+u ∧ i < S) ↔ (M+u < S ∧ i=M+u) := by omega
      by_cases physical : i=M+u ∧ i < S
      · rw [if_pos physical,if_pos (cond.mp physical)]
      · rw [if_neg physical,if_neg (fun h=>physical (cond.mpr h))]
    · have high : D 12 < i := by omega
      have d5:=mono 5 12 (by decide) (by decide)
      have d12:=mono 0 12 (by decide) (by decide)
      have hole : ¬(i=M+u ∧ i < S) := by omega
      have four : ¬(D 4 < i ∧ i < D 5) := by omega
      have eleven : ¬(D 11 < i ∧ i < D 12) := by omega
      change (if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else
        if D 11 < i ∧ i < D 12 then _ else T i)=(if M+u < S ∧ i=M+u then none else base i)
      rw [if_neg hole,if_neg four,if_neg eleven,if_neg (by omega : ¬(M+u < S ∧ i=M+u))]
      exact rep.outside i outside
  · exact grid_blank (memory_grid rep.context u)
  · intro j hj i lo hi
    have choices : j=0 ∨ j=2 ∨ j=3 ∨ j=7 := by simpa using hj
    rcases choices with rfl | rfl | rfl | rfl
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.originalQuota i lo hi
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.ell i lo hi
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.originalWindow i lo hi
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.anchor i lo hi
/-- The ONE abort cleanup consumer, usable after any native decoder failure.
It restores the complete original image, not just the source cell or verdict. -/
private theorem AbortFrame.cleanup {base T S L H Q F r M W n g u source beta}
    (rep : AbortFrame base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u source beta)
    (N B P : Nat) (room : SerializedBody.delimiter F r n 12 ≤ P) (fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B) :
    ∃ t,t ≤ 512*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+u)),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.machine.reject,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ : Config 7500 N B) := by
  let D:=SerializedBody.delimiter F r n
  let U:=memory T D S M W u
  have ctx:=rep.context
  have before:=ctx.before
  have grid:=memory_grid ctx u
  have restoredEq:=rep.restored_eq
  rcases ctx with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
  change S < D 0 at before
  change D 0=F+1 at anchor
  change ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b at mono
  have hb : H < D 0 := by omega
  have header (i : Nat) (lo : S ≤ i) (hi : i < D 0) : U i=T i := by
    change memory T D S M W u i=T i
    rw [memory_below mono hi,if_neg (by omega : ¬(i=M+u ∧ i < S))]
  obtain ⟨t,price,run,prefixBound⟩:=SerializedBodyCompletion.abort_cleanup D U S L H Q F (M+u) N B P source
    sl lh positive arena anchor rise mono (grid_blank grid) (grid_cells grid) room fit h0 hH
    (by rw [header S le_rfl before];exact eof) (by rw [header L (by omega) (by omega)];exact left)
    (by rw [header H (by omega) hb];exact right) (by rw [header F (by omega) (by omega)];exact fence)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact reg i il ih)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact ass i il ih)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact marks i il ih)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact gap i il ih)
    (by intro physical;change (if M+u=M+u ∧ M+u < S then none else _)=none;exact if_pos ⟨rfl,physical⟩)
    (by
      intro i il ih
      change memory T D S M W u i=some (source ⟨i,ih⟩)
      rw [memory_below mono (by omega),if_neg (by omega : ¬(i=M+u ∧ i < S))]
      exact src i (by omega) ih)
  change SerializedBody.machine.run t _=⟨SerializedBody.machine.reject,⟨H,hH⟩,
    fun i=>restored U D source (M+u) i.val⟩ at run
  rw [restoredEq] at run
  exact ⟨t,price,run,prefixBound⟩
private theorem Context.withBuffer : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ bits,D 9+1+2*bits.length ≤ D 10 →
    Context D (place T (D 9+1) bits) S L H Q F r M W n source beta := by
  run_tac checkedFrom `FullBodyClosure.Input "Context.withBuffer"
private theorem place_outside : ∀ T a bits i,i < a ∨ a+2*bits.length ≤ i → place T a bits i=T i := by
  run_tac checkedFrom `FullBodyClosure.Fold "place_outside"
private theorem AbortFrame.withBuffer {base D T S L H Q F r M W n g u source beta}
    (rep : AbortFrame base D T S L H Q F r M W n g u source beta)
    (bits : List Bool) (fit : D 9+1+2*bits.length ≤ D 10) :
    AbortFrame base D (place T (D 9+1) bits) S L H Q F r M W n g u source beta := by
  have mono:=grid_mono rep.context.grid
  have same (j : Nat) (hj : j ≤ 8) (i : Nat) (il : D j < i) (ih : i < D (j+1)) :
      place T (D 9+1) bits i=T i := by
    have :=mono (j+1) 9 (by omega) (by decide)
    exact place_outside T _ bits i (Or.inl (by omega))
  refine ⟨rep.context.withBuffer bits fit,?_,rep.cursor,?_,?_,?_,?_⟩
  · intro i outside
    have :=mono 0 9 (by decide) (by decide)
    have :=mono 10 12 (by decide) (by decide)
    rw [place_outside T _ bits i (by omega)]
    exact rep.outside i outside
  · intro i il ih;rw [same 0 (by decide) i il ih];exact rep.originalQuota i il ih
  · intro i il ih;rw [same 2 (by decide) i il ih];exact rep.ell i il ih
  · intro i il ih;rw [same 3 (by decide) i il ih];exact rep.originalWindow i il ih
  · intro i il ih;rw [same 7 (by decide) i il ih];exact rep.anchor i il ih
private theorem memory_place : ∀ {D T S L H Q F r M W n source beta},
    Context D T S L H Q F r M W n source beta → ∀ a u bits,D 9 < a → a+2*bits.length ≤ D 10 →
    place (memory T D S M W u) a bits=memory (place T a bits) D S M W u := by
  run_tac checkedFrom `FullBodyClosure.Input "memory_place"
private theorem input_full : ∀ {D T S L H Q F r M W n source beta}
    (_ctx : Context D T S L H Q F r M W n source beta) (u N B P ell : Nat)
    (_len1 : D 2=D 1+n+1) (_len2 : D 3=D 2+r+1) (_len8 : D 9=D 8+n+1) (_len9 : D 10=D 9+2*r+1)
    (_small : ell ≤ n) (_bound : ell ≤ r) (_u2 : Unary D T 2 ell) (_u1 : Unary D T 1 0) (_u8 : Unary D T 8 0)
    (_free : ∀ i,D 9 < i → i < D 10 → T i=some false) (_cursor : u ≤ W)
    (_room : D 12 ≤ P) (_fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B),
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
  run_tac checkedFrom `FullBodyClosure.Operand "input_full"
private abbrev DecRows : Nat → Fin 7500 → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "DecRows"
private abbrev IncRows : Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "IncRows"
private abbrev NeedRows : Fin 3 → Prop := by run_tac checkedKernel "NeedRows"
private theorem needs_actual : ∀ m,NeedRows m := by run_tac checkedKernel "needs_actual"
private theorem need_rows : ∀ m,∃ de inc tag : Fin 7500,
    SerializedBody.machine.step (SerializedBodyCompletion.needEntry m) none=(de,none,.stay) ∧
    DecRows 6 de (SerializedBodyRefinement.getAbort m) inc ∧ IncRows 5 inc tag ∧
    4 ≤ tag.val ∧ SerializedBody.machine.step tag none=(SerializedBodyRefinement.getEntry 0 m,none,.stay) :=
  needs_actual
private theorem keep : ∀ {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (mv : Move),
    h ≤ P → h' ≤ P → 4 ≤ s.val → SerializedBody.machine.step s (T h)=(s',T h,mv) →
    (match mv with | .left=>h-1 | .stay=>h | .right=>h+1)=h' →
    Path P 1 (node s h T) (node s' h' T) := by run_tac checkedKernel "keep"
private theorem dec_zero : ∀ {D T j w P start zero pos},Grid D T → j < 12 → D 12 ≤ P →
    D (j+1)=D j+w+1 → Unary D T j 0 → DecRows j start zero pos →
    Path P (2*(D j-D 0+j)+3) (node start (D 0) T) (node zero (D 0) T) := by
  run_tac checkedKernel "dec_zero"
private theorem need_zero {D T P r} (m : Fin 3) (grid : Grid D T) (room : D 12 ≤ P)
    (len6 : D 7=D 6+r+1) (zero : Unary D T 6 0) :
    ∃ t,t ≤ 64*(P+1) ∧ Path P t
      (node (SerializedBodyCompletion.needEntry m) (D 0) T)
      (node (SerializedBodyRefinement.getAbort m) (D 0) T) := by
  obtain ⟨de,inc,tag,row,dec,_inc,_tag,_last⟩:=need_rows m
  have root:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
  have q6:=le_trans (grid_mono grid 6 12 (by decide) (by decide)) room
  have first:=keep (SerializedBodyCompletion.needEntry m) de (D 0) (D 0) T .stay root root
    (by fin_cases m <;> decide) (by rw [grid_blank grid 0 (by decide)];exact row) rfl
  have last:=dec_zero grid (by decide) room len6 zero dec
  exact ⟨_,by omega,first.append last⟩
/-- Internal zero-quota Need, with arbitrary continuation stack and cursor.
The literal cleanup is composed once at its actual witnessed time. -/
private theorem Rep.emptyQuota {base T S L H Q F r M W n g u v source beta K}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (exhausted : g=v) (N B P : Nat) (room : SerializedBody.delimiter F r n 12 ≤ P)
    (fit : P < tapeLength N B) (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B)
    (hH : H < tapeLength N B) :
    ∃ t,t ≤ 576*(P+1) ∧ Native t
      (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.machine.reject,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ : Config 7500 N B) := by
  have zero:=memory_unary rep.context u (by decide) (by decide) (by decide) rep.quota
  rw [exhausted,Nat.sub_self] at zero
  have len6 : SerializedBody.delimiter F r n 7=SerializedBody.delimiter F r n 6+r+1 := by
    change F+6*r+n+8=F+5*r+n+7+r+1;omega
  obtain ⟨a,pa,path⟩:=need_zero (SerializedBody.sourceMode source (M+u)) (memory_grid rep.context u) room len6 zero
  obtain ⟨b,pb,last⟩:=rep.abortFrame.cleanup N B P room fit h0 hH
  exact ⟨a+b,by omega,native_trans ⟨path.execute fit,path.prefix fit⟩ last⟩
/-- Internal Need with an incomplete tag: paid node opening, all remaining real
Get callbacks/stays, exhausted Get and complete reject cleanup on the same table. -/
private theorem Rep.shortTag {base T S L H Q F r M W n g u v source beta K}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (paid : v < g) (short : W < u+3) (N B P : Nat) (room : SerializedBody.delimiter F r n 12 ≤ P)
    (fit : P < tapeLength N B) (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B)
    (hH : H < tapeLength N B) :
    ∃ t,t ≤ 896*(P+1) ∧ Native t
      (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.machine.reject,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ : Config 7500 N B) := by
  let D:=SerializedBody.delimiter F r n
  have len5 : D 6=D 5+r+1 := by change F+5*r+n+7=F+4*r+n+6+r+1;omega
  have len6 : D 7=D 6+r+1 := by change F+6*r+n+8=F+5*r+n+7+r+1;omega
  have len10 : D 11=D 10+3*r+4 := by change F+12*r+2*n+15=F+9*r+2*n+11+3*r+4;omega
  obtain ⟨a,pa,first,opened⟩:=rep.need paid len5 len6 len10 N B P room fit h0
  obtain ⟨b,pb,middle⟩:=tag_total opened.context u N B P opened.cursor room fit h0
  simp only [show ¬u+3 ≤ W by omega,↓reduceIte] at middle
  obtain ⟨c,pc,last⟩:=(opened.abortFrame.advance (u':=W) le_rfl).cleanup N B P room fit h0 hH
  exact ⟨a+b+c,by omega,native_trans (native_trans first middle) last⟩
/-- The real native Need dispatch, with literal terminal failures. This is one
branch of the shared recurrence, not a theorem about the complete decoder. -/
private theorem Rep.needStep {base T S L H Q F r M W n g u v source beta K}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (N B P : Nat) (room : SerializedBody.delimiter F r n 12 ≤ P) (fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B) :
    let D:=SerializedBody.delimiter F r n
    let initial : Config 7500 N B:=⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),
      ⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
    ∃ t,t ≤ 896*(P+1) ∧
      if g=v then Native t initial
        ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩
      else if u+3 ≤ W then ∃ U,
        Native t initial
          ⟨tagDestination (SerializedBody.sourceMode source (M+(u+3)))
            (padRead source (M+u)) (padRead source (M+(u+1))) (padRead source (M+(u+2))),⟨D 0,h0⟩,
            fun i=>memory U D S M W (u+3) i.val⟩ ∧
        Rep base D U S L H Q F r M W n g (u+3) (v+1) source beta K
      else Native t initial
        ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ := by
  dsimp only
  by_cases empty : g=v
  · obtain ⟨t,price,run⟩:=rep.emptyQuota empty N B P room fit h0 hH
    exact ⟨t,by omega,by simpa only [if_pos empty] using run⟩
  have paid : v < g := by have :=rep.seen;omega
  by_cases enough : u+3 ≤ W
  · let D:=SerializedBody.delimiter F r n
    have len5 : D 6=D 5+r+1 := by change F+5*r+n+7=F+4*r+n+6+r+1;omega
    have len6 : D 7=D 6+r+1 := by change F+6*r+n+8=F+5*r+n+7+r+1;omega
    have len10 : D 11=D 10+3*r+4 := by change F+12*r+2*n+15=F+9*r+2*n+11+3*r+4;omega
    obtain ⟨a,pa,first,opened⟩:=rep.need paid len5 len6 len10 N B P room fit h0
    obtain ⟨b,pb,last⟩:=tag_total opened.context u N B P opened.cursor room fit h0
    simp only [if_pos enough] at last
    refine ⟨a+b,by omega,?_⟩
    simp only [if_neg empty,if_pos enough]
    exact ⟨_,native_trans first last,opened.advance enough⟩
  · obtain ⟨t,price,run⟩:=rep.shortTag paid (by omega) N B P room fit h0 hH
    exact ⟨t,price,by simpa only [if_neg empty,if_neg enough] using run⟩
/-- Proof specification of the seven saved continuations; never runtime data. -/
private def returnNext (c : Fin 7) (b : Bool) : Sum (Fin 7) Bool :=
  match c.val with
  | 0 => .inr (!b)
  | 1 => .inl (if b then 3 else 2)
  | 2 => .inr false
  | 3 => .inr b
  | 4 => .inl (if b then 6 else 5)
  | 5 => .inr b
  | _ => .inr true
private theorem return_control (m : Fin 3) (b : Bool) (c : Fin 7) :
    popNextState m b c=match returnNext c b with
      | .inl saved=>pushState m saved
      | .inr value=>returnState m value := by
  fin_cases m <;> cases b <;> fin_cases c <;> rfl
/-- All seven actual Return continuations on the shared frame. Left returns
really push a saved Boolean and enter Need for the OTHER child. -/
private theorem Rep.returnStep {base D T S L H Q F r M W n g u v source beta K}
    (c : Fin 7) (rep : Rep base D T S L H Q F r M W n g u v source beta (K++[c]))
    (b : Bool) (len10 : D 11=D 10+3*r+4)
    (N B P : Nat) (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t ≤ 256*(P+1) ∧ ∃ U,
      match returnNext c b with
      | .inl saved=>Native t
          (⟨returnState (SerializedBody.sourceMode source (M+u)) b,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
          (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
            fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
          Rep base D U S L H Q F r M W n g u v source beta (K++[saved])
      | .inr value=>Native t
          (⟨returnState (SerializedBody.sourceMode source (M+u)) b,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
          (⟨returnState (SerializedBody.sourceMode source (M+u)) value,⟨D 0,h0⟩,
            fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
          Rep base D U S L H Q F r M W n g u v source beta K := by
  have depth : K.length+1 ≤ v := by simpa using rep.depth
  obtain ⟨a,pa,first,popped⟩:=rep.pop c b len10 N B P room fit h0
  have control:=return_control (SerializedBody.sourceMode source (M+u)) b c
  cases branch : returnNext c b with
  | inl saved =>
    simp only [branch] at control ⊢
    rw [control] at first
    obtain ⟨d,pd,last,pushed⟩:=popped.push saved depth len10 N B P room fit h0
    exact ⟨a+d,by omega,_,native_trans first last,pushed⟩
  | inr value =>
    simp only [branch] at control ⊢
    rw [control] at first
    exact ⟨a,by omega,_,first,popped⟩
/-- A decreasing bound on native MACRO transitions, not a tape-time claim. -/
private def rank (g v depth : Nat) (returning : Bool) : Nat :=
  3*(g-v)+2*depth+(if returning then 1 else 0)
private theorem rank_need_return {g v depth} (paid : v < g) :
    rank g (v+1) depth true < rank g v depth false := by
  unfold rank
  simp only [↓reduceIte,Bool.false_eq_true]
  omega
private theorem rank_need_child {g v depth} (paid : v < g) :
    rank g (v+1) (depth+1) false < rank g v depth false := by
  unfold rank
  simp only [Bool.false_eq_true,↓reduceIte]
  omega
private theorem rank_return_left (g v depth : Nat) :
    rank g v (depth+1) false < rank g v (depth+1) true := by
  unfold rank
  simp only [Bool.false_eq_true,↓reduceIte]
  omega
private theorem rank_return_right (g v depth : Nat) :
    rank g v depth true < rank g v (depth+1) true := by
  unfold rank
  simp only [↓reduceIte]
  omega
private abbrev paint : (Nat → Option Bool) → Nat → Nat → Bool → Nat → Option Bool := by run_tac checkedKernel "paint"
private abbrev scrub : (Nat → Nat) → List (Nat × Bool) → (Nat → Option Bool) → Nat → Option Bool := by run_tac checkedKernel "scrub"
private abbrev successEdits : List (Nat × Bool) := by run_tac checkedFrom `FullBodyClosure.Return "successEdits"
private theorem paint_cell {D : Nat → Nat} (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (T : Nat → Option Bool) (j k i : Nat) (b : Bool) (hj : j < 12) (hk : k < 12)
    (rise : D k < D (k+1)) (lo : D j < i) (hi : i < D (j+1)) :
    paint T (D k+1) (D (k+1)-D k-1) b i=(if j=k then some b else T i) := by
  by_cases same : j=k
  · subst k
    change (if D j+1 ≤ i ∧ i < D j+1+(D (j+1)-D j-1) then some b else T i)=_
    rw [if_pos (by omega),if_pos rfl]
  · have outside:=outside_field mono hj hk same ⟨lo,hi⟩
    change (if D k+1 ≤ i ∧ i < D k+1+(D (k+1)-D k-1) then some b else T i)=_
    rw [if_neg (by omega),if_neg same]
private theorem paint_blank {D : Nat → Nat} (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (T : Nat → Option Bool) (j k : Nat) (b : Bool) (hj : j ≤ 12) (hk : k < 12)
    (rise : D k < D (k+1)) : paint T (D k+1) (D (k+1)-D k-1) b (D j)=T (D j) := by
  have out : D j ≤ D k ∨ D (k+1) ≤ D j := by
    by_cases order : j ≤ k
    · exact Or.inl (mono j k order (by omega))
    · exact Or.inr (mono (k+1) j (by omega) hj)
  change (if D k+1 ≤ D j ∧ D j < D k+1+(D (k+1)-D k-1) then _ else T (D j))=T (D j)
  exact if_neg (by omega)
private theorem paint_out {D : Nat → Nat} (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (T : Nat → Option Bool) (k i : Nat) (b : Bool) (hk : k < 12)
    (rise : D k < D (k+1)) (out : i < D 0 ∨ D 12 < i) :
    paint T (D k+1) (D (k+1)-D k-1) b i=T i := by
  have :=mono 0 k (by omega) (by omega)
  have :=mono (k+1) 12 (by omega) (by decide)
  change (if D k+1 ≤ i ∧ i < D k+1+(D (k+1)-D k-1) then _ else T i)=T i
  exact if_neg (by omega)
private def editedValue : List (Nat × Bool) → Nat → Option Bool → Option Bool
  | [],_,old=>old
  | (k,b)::xs,j,old=>editedValue xs j (if j=k then some b else old)
private theorem scrub_field {D T} (grid : Grid D T) (edits : List (Nat × Bool))
    (bound : ∀ x∈edits,x.1 < 12) (j i : Nat) (hj : j < 12) (lo : D j < i) (hi : i < D (j+1)) :
    scrub D edits T i=editedValue edits j (T i) := by
  have rise:=grid_rise grid
  have mono:=grid_mono grid
  suffices claim : ∀ T : Nat → Option Bool,scrub D edits T i=editedValue edits j (T i) from claim T
  induction edits with
  | nil => intro T;rfl
  | cons x xs ih =>
    rcases x with ⟨k,b⟩
    intro T
    change scrub D xs (paint T (D k+1) (D (k+1)-D k-1) b) i=_
    rw [ih (by intro x hx;exact bound x (List.mem_cons_of_mem _ hx))]
    rw [paint_cell mono T j k i b hj (bound (k,b) (List.mem_cons_self)) (rise k (bound (k,b) (List.mem_cons_self))) lo hi]
    rfl
private theorem scrub_blank {D T} (grid : Grid D T) (edits : List (Nat × Bool))
    (bound : ∀ x∈edits,x.1 < 12) (j : Nat) (hj : j ≤ 12) : scrub D edits T (D j)=T (D j) := by
  have rise:=grid_rise grid
  have mono:=grid_mono grid
  suffices claim : ∀ T : Nat → Option Bool,scrub D edits T (D j)=T (D j) from claim T
  induction edits with
  | nil => intro T;rfl
  | cons x xs ih =>
    rcases x with ⟨k,b⟩
    intro T
    change scrub D xs (paint T (D k+1) (D (k+1)-D k-1) b) (D j)=_
    rw [ih (by intro x hx;exact bound x (List.mem_cons_of_mem _ hx))]
    exact paint_blank mono T j k b hj (bound (k,b) (List.mem_cons_self)) (rise k (bound (k,b) (List.mem_cons_self)))
private theorem scrub_out {D T} (grid : Grid D T) (edits : List (Nat × Bool))
    (bound : ∀ x∈edits,x.1 < 12) (i : Nat) (out : i < D 0 ∨ D 12 < i) : scrub D edits T i=T i := by
  have rise:=grid_rise grid
  have mono:=grid_mono grid
  suffices claim : ∀ T : Nat → Option Bool,scrub D edits T i=T i from claim T
  induction edits with
  | nil => intro T;rfl
  | cons x xs ih =>
    rcases x with ⟨k,b⟩
    intro T
    change scrub D xs (paint T (D k+1) (D (k+1)-D k-1) b) i=_
    rw [ih (by intro x hx;exact bound x (List.mem_cons_of_mem _ hx))]
    exact paint_out mono T k i b (bound (k,b) (List.mem_cons_self)) (rise k (bound (k,b) (List.mem_cons_self))) out
private theorem success_bound : ∀ jb∈successEdits,jb.1 < 12 := by
  run_tac checkedFrom `FullBodyClosure.Return "successEdits_bound"
private theorem image_ext : ∀ (base T : Nat → Option Bool) (F r n g W a v u rem quota : Nat),
    (∀ i,i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i → T i=base i) →
    (∀ j,j ≤ 12 → T (SerializedBody.delimiter F r n j)=none) →
    (∀ j i,j < 12 → SerializedBody.delimiter F r n j < i → i < SerializedBody.delimiter F r n (j+1) →
      T i=some (value F r n g W a v u rem quota j i)) →
    T=SerializedBody.image base F r n g W a v u rem quota := by
  run_tac checkedFrom `FullBodyClosure.Frame "image_ext"
private theorem memory_end_fields {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (u : Nat) :
    Unary D (memory T D S M W u) 4 (W-u) ∧ Unary D (memory T D S M W u) 11 u := by
  have mono:=grid_mono ctx.grid
  have before:=ctx.before
  constructor
  · intro i lo hi
    have :=mono 0 4 (by decide) (by decide)
    change (if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else _)=_
    rw [if_neg (by omega : ¬(i=M+u ∧ i < S)),if_pos ⟨lo,hi⟩]
  · intro i lo hi
    have :=mono 0 11 (by decide) (by decide)
    have apart:=outside_field mono (by decide : 11 < 12) (by decide : 4 < 12) (by decide : 11≠4) ⟨lo,hi⟩
    change (if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else
      if D 11 < i ∧ i < D 12 then _ else _)=_
    rw [if_neg (by omega : ¬(i=M+u ∧ i < S)),if_neg apart,if_pos ⟨lo,hi⟩]
private theorem Rep.successImage {base T S L H Q F r M W n g u v source beta K}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K) :
    let D:=SerializedBody.delimiter F r n
    let U:=scrub D successEdits (memory T D S M W u)
    (if M+u < S then put U (M+u) (some (padRead source (M+u))) else U)=
      SerializedBody.image base F r n g W (S-min M S) v u (W-u) 0 := by
  dsimp only
  let D:=SerializedBody.delimiter F r n
  let U:=memory T D S M W u
  have grid:=memory_grid rep.context u
  have mono:=grid_mono grid
  change ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b at mono
  have before:=rep.context.before
  change S < D 0 at before
  have exterior (i : Nat) (out : i < D 0 ∨ D 12 < i) :
      U i=(if i=M+u ∧ i < S then none else base i) := by
    by_cases low : i < D 0
    · change memory T D S M W u i=_
      rw [memory_below mono low,rep.outside i out]
    · have high : D 12 < i := by omega
      have :=mono 5 12 (by decide) (by decide)
      have :=mono 0 12 (by decide) (by decide)
      change (if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then _ else
        if D 11 < i ∧ i < D 12 then _ else T i)=_
      rw [if_neg (by omega : ¬(D 4 < i ∧ i < D 5)),if_neg (by omega : ¬(D 11 < i ∧ i < D 12)),rep.outside i out]
  have physicalCell (physical : M+u < S) : base (M+u)=some (padRead source (M+u)) := by
    have eq:=rep.outside (M+u) (Or.inl (by change M+u < D 0;omega))
    rcases rep.context with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
    rw [←eq,src _ (by omega) physical]
    simp only [padRead,physical,↓reduceDIte]
  have unpatched (i : Nat) (high : S ≤ i) :
      (if M+u < S then put (scrub D successEdits U) (M+u) (some (padRead source (M+u))) else scrub D successEdits U) i=
        scrub D successEdits U i := by
    by_cases physical : M+u < S
    · rw [if_pos physical]
      change (if i=M+u then _ else scrub D successEdits U i)=_
      exact if_neg (by omega)
    · rw [if_neg physical]
  apply image_ext base _ F r n g W (S-min M S) v u (W-u) 0
  · intro i out
    change i < D 0 ∨ D 12 < i at out
    by_cases physical : M+u < S
    · rw [if_pos physical]
      by_cases current : i=M+u
      · subst i
        change (if M+u=M+u then _ else _)=_
        rw [if_pos rfl,physicalCell physical]
      · change (if i=M+u then _ else scrub D successEdits U i)=base i
        rw [if_neg current,scrub_out grid successEdits success_bound i out]
        change U i=base i
        rw [exterior i out,if_neg (by omega : ¬(i=M+u ∧ i < S))]
    · rw [if_neg physical,scrub_out grid successEdits success_bound i out]
      change U i=base i
      rw [exterior i out,if_neg (by omega : ¬(i=M+u ∧ i < S))]
  · intro j hj
    have lo:=mono 0 j (by omega) hj
    rw [unpatched (D j) (by omega),scrub_blank grid successEdits success_bound j hj,grid_blank grid j hj]
  · intro j i hj lo hi
    change D j < i at lo
    change i < D (j+1) at hi
    have low:=mono 0 j (by omega) (by omega)
    rw [unpatched i (by omega),scrub_field grid successEdits success_bound j i hj lo hi]
    interval_cases j
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.originalQuota i lo hi
    · rfl
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.ell i lo hi
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.originalWindow i lo hi
    · exact (memory_end_fields rep.context u).1 i lo hi
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.nodes i lo hi
    · change some false=some (decide (i-D 6 ≤ 0))
      simp only [show ¬i-D 6 ≤ 0 by omega,decide_false]
    · exact memory_unary rep.context u (by decide) (by decide) (by decide) rep.anchor i lo hi
    · rfl
    · rfl
    · rfl
    · exact (memory_end_fields rep.context u).2 i lo hi
private abbrev ReturnRows : Fin 3 → Bool → Prop := by run_tac checkedFrom `FullBodyClosure.Return "ReturnRows"
private theorem return_actual (m : Fin 3) (b : Bool) : ReturnRows m b := by
  cases b <;> fin_cases m
  · run_tac checkedFrom `FullBodyClosure.Rows0 "returnRows0_0"
  · run_tac checkedFrom `FullBodyClosure.Rows1 "returnRows1_0"
  · run_tac checkedFrom `FullBodyClosure.Rows2 "returnRows2_0"
  · run_tac checkedFrom `FullBodyClosure.Rows0 "returnRows0_1"
  · run_tac checkedFrom `FullBodyClosure.Rows1 "returnRows1_1"
  · run_tac checkedFrom `FullBodyClosure.Rows2 "returnRows2_1"
private theorem return_empty_path : ∀ (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F c P : Nat) (source : Fin S → Bool) (b : Bool),
    Grid D T → S < L → L < H → 0 < Q → H+Q < F → D 0=F+1 → D 12 ≤ P → D 10+4 ≤ D 11 →
    (∀ i,D 10 < i → i < D 11 → T i=some true) → T S=none → T L=none → T H=none → T F=some false →
    (c < S → T c=none) → (∀ i,S < i → i < L → ∃ v,T i=some v) →
    (∀ i,L < i → i < H → ∃ v,T i=some v) → (∀ i,H < i → i ≤ H+Q → T i=some true) →
    (∀ i,H+Q < i → i < F → T i=none) → (∀ i,c < i → i < S → ∃ v,T i=some v) →
    ReturnRows (SerializedBody.sourceMode source c) b →
    let U:=scrub D successEdits T
    let V:=if c < S then put U c (some (padRead source c)) else U
    ∃ t,t ≤ 512*(P+1) ∧ Path P t (node (returnState (SerializedBody.sourceMode source c) b) (D 0) T)
      (node (SerializedBody.done b) H V) := by run_tac checkedFrom `FullBodyClosure.Return "return_empty_path"
private theorem Rep.finish {base T S L H Q F r M W n g u v source beta}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta [])
    (b : Bool) (N B P : Nat) (room : SerializedBody.delimiter F r n 12 ≤ P) (fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B) :
    ∃ t,t ≤ 512*(P+1) ∧ Native t
      (⟨returnState (SerializedBody.sourceMode source (M+u)) b,⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.done b,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) v u (W-u) 0 i.val⟩ : Config 7500 N B) := by
  let D:=SerializedBody.delimiter F r n
  let U:=memory T D S M W u
  have ctx:=rep.context
  have grid:=memory_grid ctx u
  have imageEq:=rep.successImage
  have stack (i : Nat) (lo : D 10 < i) (hi : i < D 11) : U i=some true := by
    have coords : D 10+1+3*((i-D 10-1)/3)+(i-D 10-1)%3=i := by omega
    have bound : (i-D 10-1)/3 ≤ r := by
      change i < F+12*r+2*n+15 at hi
      change F+9*r+2*n+11 < i at lo
      change (i-(F+9*r+2*n+11)-1)/3 ≤ r
      omega
    change memory T D S M W u i=some true
    rw [←coords,memory_field ctx u 10 _ (by decide) (by decide) (by decide)
      (by change D 10 < _;omega) (by change _ < D 11;omega)]
    exact rep.stack _ bound _ (by omega)
  have before:=ctx.before
  change S < D 0 at before
  rcases ctx with ⟨sl,lh,width,positive,arena,anchor,rise,mono,blank,cells,len4,len11,hw,eof,left,right,fence,reg,ass,betaCells,marks,gap,src⟩
  change D 0=F+1 at anchor
  change ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b at mono
  have hb : H < D 0 := by omega
  have header (i : Nat) (lo : S ≤ i) (hi : i < D 0) : U i=T i := by
    change memory T D S M W u i=T i
    rw [memory_below mono hi,if_neg (by omega : ¬(i=M+u ∧ i < S))]
  obtain ⟨t,price,path⟩:=return_empty_path D U S L H Q F (M+u) P source b grid sl lh positive arena anchor room
    (by change F+9*r+2*n+11+4 ≤ F+12*r+2*n+15;omega) stack
    (by rw [header S le_rfl before];exact eof) (by rw [header L (by omega) (by omega)];exact left)
    (by rw [header H (by omega) hb];exact right) (by rw [header F (by omega) (by omega)];exact fence)
    (by intro physical;change (if M+u=M+u ∧ M+u < S then none else _)=none;exact if_pos ⟨rfl,physical⟩)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact reg i il ih)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact ass i il ih)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact marks i il ih)
    (by intro i il ih;rw [header i (by omega) (by omega)];exact gap i il ih)
    (by
      intro i il ih
      change ∃ b,memory T D S M W u i=some b
      rw [memory_below mono (by omega),if_neg (by omega : ¬(i=M+u ∧ i < S))]
      exact ⟨source ⟨i,ih⟩,src i (by omega) ih⟩)
    (return_actual _ b)
  rw [imageEq] at path
  exact ⟨t,price,path.execute fit,path.prefix fit⟩
private theorem const_row : ∀ m,SerializedBody.machine.step (constState m) none=
    (SerializedBodyRefinement.getEntry 7 m,none,.stay) := by run_tac checkedFrom `FullBodyClosure.NodeRows "const_row"
private theorem const_exit : ∀ b m,SerializedBodyRefinement.getExit 7 b m=returnState m b := by
  run_tac checkedFrom `FullBodyClosure.NodeRows "const_exit"
private theorem const_safe : ∀ m,4 ≤ (constState m).val := by run_tac checkedFrom `FullBodyClosure.NodeRows "const_safe"
private theorem Rep.constant {base T S L H Q F r M W n g u v source beta K}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (N B P : Nat) (room : SerializedBody.delimiter F r n 12 ≤ P) (fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B) :
    let D:=SerializedBody.delimiter F r n
    let initial : Config 7500 N B:=⟨constState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
    ∃ t,t ≤ 640*(P+1) ∧
      if u < W then Native t initial
        ⟨returnState (SerializedBody.sourceMode source (M+(u+1))) (padRead source (M+u)),⟨D 0,h0⟩,
          fun i=>memory T D S M W (u+1) i.val⟩ ∧
        Rep base D T S L H Q F r M W n g (u+1) v source beta K
      else Native t initial
        ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ := by
  let D:=SerializedBody.delimiter F r n
  have jump:=native_stay (constState (SerializedBody.sourceMode source (M+u)))
    (SerializedBodyRefinement.getEntry 7 (SerializedBody.sourceMode source (M+u))) (memory T D S M W u) ⟨D 0,h0⟩
    (grid_blank (memory_grid rep.context u) 0 (by decide))
    (const_safe (SerializedBody.sourceMode source (M+u))) (const_row (SerializedBody.sourceMode source (M+u)))
  by_cases positive : u < W
  · obtain ⟨t,price,last⟩:=read_plain rep.context u N B P 7 positive room fit h0
    rw [const_exit] at last
    refine ⟨1+t,by omega,?_⟩
    simp only [if_pos positive]
    exact ⟨native_trans jump last,rep.advance (by omega)⟩
  · have final : u=W := by have :=rep.cursor;omega
    subst u
    obtain ⟨a,pa,middle⟩:=empty_get rep.context N B P 7 (SerializedBody.sourceMode source (M+W)) room fit h0
    obtain ⟨b,pb,last⟩:=rep.abortFrame.cleanup N B P room fit h0 hH
    refine ⟨1+a+b,by omega,?_⟩
    simp only [if_neg positive]
    exact native_trans (native_trans jump middle) last
private theorem ell_small (n : Nat) : bitLength n ≤ n := bitLength_le_self n
private theorem leaf_price (r n P ell a b : Nat) (small : ell ≤ r)
    (pa : a ≤ 8192*(ell+1)*(n+1)*(P+1)) (pb : b ≤ 512*(P+1)) :
    a+b ≤ 9216*(r+1)*(n+1)*(P+1) := by
  have first:=Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_right (n+1) (Nat.mul_le_mul_left 8192 (Nat.succ_le_succ small)))
  have second : P+1 ≤ (r+1)*(n+1)*(P+1) := by
    have factor : 0 < (r+1)*(n+1) := Nat.mul_pos (by omega) (by omega)
    exact Nat.le_mul_of_pos_left _ factor
  nlinarith
/-- Whole input operand as a recurrence action: every failure is now a literal
reject with the complete original image, not a live abort or default false. -/
private theorem Rep.inputStep {base T S L H Q F r M W n g u v source beta K}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (N B P : Nat) (room : SerializedBody.delimiter F r n 12 ≤ P) (fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B) :
    let D:=SerializedBody.delimiter F r n
    let ell:=bitLength n
    let payload:=SerializedBody.window source (M+u) ell
    let initial : Config 7500 N B:=⟨inputState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
    let rejected : Config 7500 N B:=⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩
    ∃ t,t ≤ 9216*(r+1)*(n+1)*(P+1) ∧
      if n=0 then Native t initial rejected
      else if ell ≤ W-u then
        if inside : numeral payload < n then Native t initial
          ⟨returnState (SerializedBody.sourceMode source (M+(u+ell))) (beta ⟨numeral payload,inside⟩),⟨D 0,h0⟩,
            fun i=>memory T D S M W (u+ell) i.val⟩ ∧
          Rep base D T S L H Q F r M W n g (u+ell) v source beta K
        else Native t initial rejected
      else Native t initial rejected := by
  let D:=SerializedBody.delimiter F r n
  have len1 : D 2=D 1+n+1 := by change F+r+n+3=F+r+2+n+1;omega
  have len2 : D 3=D 2+r+1 := by change F+2*r+n+4=F+r+n+3+r+1;omega
  have len8 : D 9=D 8+n+1 := by change F+7*r+2*n+10=F+7*r+n+9+n+1;omega
  have len9 : D 10=D 9+2*r+1 := by change F+9*r+2*n+11=F+7*r+2*n+10+2*r+1;omega
  obtain ⟨a,pa,operand⟩:=input_full rep.context u N B P (bitLength n) len1 len2 len8 len9 (ell_small n) rep.ellBound
    rep.ell rep.index rep.j rep.buffer rep.cursor room fit h0
  dsimp only at operand ⊢
  by_cases zero : n=0
  · simp only [if_pos zero] at operand ⊢
    obtain ⟨b,pb,cleanup⟩:=rep.abortFrame.cleanup N B P room fit h0 hH
    exact ⟨a+b,leaf_price r n P (bitLength n) a b rep.ellBound pa pb,native_trans operand cleanup⟩
  by_cases enough : (bitLength n) ≤ W-u
  · simp only [if_neg zero,if_pos enough] at operand ⊢
    by_cases inside : numeral (SerializedBody.window source (M+u) (bitLength n)) < n
    · simp only [dif_pos inside] at operand ⊢
      refine ⟨a,?_,operand,rep.advance (by have :=rep.cursor;omega)⟩
      have price:=leaf_price r n P (bitLength n) a 0 rep.ellBound pa (by omega)
      simpa only [Nat.add_zero] using price
    · simp only [dif_neg inside] at operand ⊢
      obtain ⟨rest,left,length,_leftBound,operand⟩:=operand
      have restFit : D 9+1+2*rest.length ≤ D 10 := by have :=rep.ellBound;omega
      have ctx:=rep.context.withBuffer rest restFit
      have bad:=(((rep.abortFrame.advance (u':=u+(bitLength n)) (by have :=rep.cursor;omega)).withBuffer rest restFit).withCounter
        8 n (by decide) (by decide) (by decide) (by decide) (by decide)).withCounter
        1 left (by decide) (by decide) (by decide) (by decide) (by decide)
      have eq : ij (place (memory T D S M W (u+(bitLength n))) (D 9+1) rest) D left n=
          memory (ij (place T (D 9+1) rest) D left n) D S M W (u+(bitLength n)) := by
        change counter (counter (place (memory T D S M W (u+(bitLength n))) (D 9+1) rest) D 8 n) D 1 left=_
        rw [memory_place rep.context _ _ rest (by change D 9 < D 9+1;omega) restFit,
          memory_counter ctx (u+(bitLength n)) 8 n (by decide) (by decide) (by decide),
          memory_counter (ctx.withCounter 8 n (by decide)) (u+(bitLength n)) 1 left (by decide) (by decide) (by decide)]
        rfl
      rw [eq] at operand
      obtain ⟨b,pb,cleanup⟩:=bad.cleanup N B P room fit h0 hH
      exact ⟨a+b,leaf_price r n P (bitLength n) a b rep.ellBound pa pb,native_trans operand cleanup⟩
  · simp only [if_neg zero,if_neg enough] at operand ⊢
    have shortFit : D 9+1+2*(SerializedBody.window source (M+u) (W-u)).length ≤ D 10 := by
      simp only [SerializedBody.window,List.length_ofFn]
      have :=rep.ellBound;omega
    have bad:=((rep.abortFrame.advance (u':=W) le_rfl).withBuffer
      (SerializedBody.window source (M+u) (W-u)) shortFit).withCounter 8 ((bitLength n)-(W-u)-1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨b,pb,cleanup⟩:=bad.cleanup N B P room fit h0 hH
    exact ⟨a+b,leaf_price r n P (bitLength n) a b rep.ellBound pa pb,native_trans operand cleanup⟩
end FullBodyClosure
