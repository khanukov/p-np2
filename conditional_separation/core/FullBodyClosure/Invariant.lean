import FullBodyClosure.Frame
import FullBodyClosure.Copy
import FullBodyClosure.Transfer
import FullBodyClosure.Guard
import FullBodyClosure.InputRows0
import FullBodyClosure.InputRows1
import FullBodyClosure.InputRows2
import FullBodyClosure.BetaRows0
import FullBodyClosure.BetaRows1
import FullBodyClosure.BetaRows2
import FullBodyClosure.BufferRows
import FullBodyClosure.BufferModel
import FullBodyClosure.IndexRows0
import FullBodyClosure.IndexRows1
import FullBodyClosure.IndexRows2
import FullBodyClosure.IndexLoop
import FullBodyClosure.IndexSemantics
import FullBodyClosure.Semantics
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
private abbrev arena : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → List (Fin 7) → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Representation "arena"
private abbrev memory : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Representation "memory"
private abbrev RepTape : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Nat → Nat → List (Fin 7) → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Representation "RepTape"
private abbrev stackBits : List (Fin 7) → Nat → Bool := by run_tac checkedFrom `FullBodyClosure.Representation "stackBits"
private theorem arena_below : ∀ {T D g v K i},(∀ a b,a    ≤    b → b    ≤    12 → D a    ≤    D b) → i < D 0 → arena T D g v K i=T i := by run_tac checkedFrom `FullBodyClosure.Representation "arena_below"
private theorem memory_below : ∀ {T D S M W u i},(∀ a b,a    ≤    b → b    ≤    12 → D a    ≤    D b) → i < D 0 → memory T D S M W u i=(if i=M+u ∧ i < S then none else T i) := by run_tac checkedFrom `FullBodyClosure.Representation "memory_below"
private theorem RepTape_below : ∀ {T D S M g W u v K i},(∀ a b,a    ≤    b → b    ≤    12 → D a    ≤    D b) → i < D 0 → RepTape T D S M g W u v K i=(if i=M+u ∧ i < S then none else T i) := by run_tac checkedFrom `FullBodyClosure.Representation "RepTape_below"
/-- Shared proof context of actual cells and addresses, with no correctness prophecy. -/
private structure Context (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r M W n : Nat) (source : Fin S → Bool) (beta : Fin n → Bool) : Prop where
  sl : S < L
  lh : L < H
  width : H=L+n+1
  positive : 0 < Q
  arena : H+Q < F
  anchor : D 0=F+1
  rise : ∀ j,j < 12 → D j < D (j+1)
  mono : ∀ a b,a    ≤    b → b    ≤    12 → D a    ≤    D b
  blank : ∀ j,j    ≤    12 → T (D j)=none
  cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b
  len4 : D 5=D 4+r+1
  len11 : D 12=D 11+r+1
  window : W    ≤    r
  eof : T S=none
  left : T L=none
  right : T H=none
  fence : T F=some false
  reg : ∀ i,S < i → i < L → ∃ b,T i=some b
  ass : ∀ i,L < i → i < H → ∃ b,T i=some b
  betaCells : ∀ j : Fin n,T (H-1-j.val)=some (beta j)
  marks : ∀ i,H < i → i    ≤    H+Q → T i=some true
  gap : ∀ i,H+Q < i → i < F → T i=none
  sourceCells : ∀ i,M    ≤    i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)
private theorem Context.before {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) : S < D 0 := by
  have :=ctx.sl;have :=ctx.lh;have :=ctx.positive;have :=ctx.arena;have :=ctx.anchor
  omega
private theorem not_delimiter {D : Nat → Nat} (mono : ∀ a b,a    ≤    b → b    ≤    12 → D a    ≤    D b)
    {j k : Nat} (hj : j < 12) (hk : k    ≤    12) : ¬(D j < D k ∧ D k < D (j+1)) := by
  by_cases order : k    ≤    j
  · have :=mono k j order (by omega);omega
  · have :=mono (j+1) k (by omega) hk;omega
private theorem arena_blank {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (g v : Nat) (K : List (Fin 7)) (j : Nat) (hj : j    ≤    12) :
    arena T D g v K (D j)=none := by
  change (if D 5 < D j ∧ D j < D 6 then _ else if D 6 < D j ∧ D j < D 7 then _ else
    if D 10 < D j ∧ D j < D 11 then _ else T (D j))=none
  rw [if_neg (not_delimiter ctx.mono (by decide : 5 < 12) hj),
    if_neg (not_delimiter ctx.mono (by decide : 6 < 12) hj),
    if_neg (not_delimiter ctx.mono (by decide : 10 < 12) hj),ctx.blank j hj]
private theorem arena_cells {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (g v : Nat) (K : List (Fin 7))
    (j i : Nat) (hj : j < 12) (lo : D j < i) (hi : i < D (j+1)) : ∃ b,arena T D g v K i=some b := by
  change ∃ b,(if D 5 < i ∧ i < D 6 then some (decide (i-D 5    ≤    v)) else
    if D 6 < i ∧ i < D 7 then some (decide (i-D 6    ≤    g-v)) else
    if D 10 < i ∧ i < D 11 then some (stackBits K (i-D 10-1)) else T i)=some b
  split_ifs with a b c
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · exact ctx.cells j i hj lo hi
/-- Direct reuse of the checked positive Get on the single shared memory image. -/
private theorem read_memory {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (g v u N B P : Nat) (K : List (Fin 7))
    (site : Fin 9) (hu : u < W) (room : D 12    ≤    P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    ∃ t,t    ≤    64*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getEntry site (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>RepTape T D S M g W u v K i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyRefinement.getExit site (padRead source (M+u)) (SerializedBody.sourceMode source (M+(u+1))),⟨D 0,h0⟩,
        fun i=>RepTape T D S M g W (u+1) v K i.val⟩ : Config 7500 N B) := by
  have before:=ctx.before
  have header (i : Nat) (_lo : S    ≤    i) (hi : i < D 0) : arena T D g v K i=T i := arena_below ctx.mono hi
  have lower (j : Nat) (hj : j    ≤    12) : D 0    ≤    D j:=ctx.mono 0 j (by omega) hj
  have rightBound : H < D 0 := by have :=ctx.positive;have :=ctx.arena;have :=ctx.anchor;omega
  obtain ⟨_bit,t,price,run,prefixBound⟩:=SerializedPositiveBody.positive_reader site D (arena T D g v K)
    S L H Q F r M W u N B P source hu ctx.window ctx.sl ctx.lh ctx.positive ctx.arena ctx.anchor
    ctx.rise ctx.mono (arena_blank ctx g v K) (arena_cells ctx g v K) ctx.len4 ctx.len11
    (by rw [header S le_rfl before];exact ctx.eof)
    (by rw [header L (by have :=ctx.sl;omega) (by have :=ctx.lh;omega)];exact ctx.left)
    (by rw [header H (by have :=ctx.sl;have :=ctx.lh;omega) rightBound];exact ctx.right)
    (by rw [header F (by have :=ctx.sl;have :=ctx.lh;have :=ctx.positive;have :=ctx.arena;omega) (by have :=ctx.anchor;omega)];exact ctx.fence)
    (by intro i lo hi;rw [header i (by omega) (by have :=ctx.lh;omega)];exact ctx.reg i lo hi)
    (by intro i lo hi;rw [header i (by have :=ctx.sl;omega) (by omega)];exact ctx.ass i lo hi)
    (by intro i lo hi;rw [header i (by have :=ctx.sl;have :=ctx.lh;omega) (by have :=ctx.arena;have :=ctx.anchor;omega)];exact ctx.marks i lo hi)
    (by intro i lo hi;rw [header i (by have :=ctx.sl;have :=ctx.lh;omega) (by have :=ctx.anchor;omega)];exact ctx.gap i lo hi)
    (by intro i lo hi;rw [arena_below ctx.mono (by omega)];exact ctx.sourceCells i lo hi) room fit h0
  refine ⟨t,price,run,?_⟩
  intro j hj
  exact prefixBound j (by omega)

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
private theorem path_native {N B P t a b} (path : Path P t a b) (fit : P < tapeLength N B) :
    Native t (embed a (lt_of_le_of_lt path.bounds.1 fit)) (embed b (lt_of_le_of_lt path.bounds.2 fit)) :=
  ⟨path.execute fit,path.prefix fit⟩
private abbrev counter : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Index "counter"
private abbrev triple : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Copy "triple"
private abbrev Twin : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Transfer "Twin"
private abbrev CopyRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Copy "CopyRows"
private abbrev TransferRows : Nat → Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Transfer "TransferRows"
private theorem copy_run : ∀ {D T P r n start out},Grid D T → D 12   ≤   P → D 3=D 2+r+1 →
    D 2=D 1+n+1 → D 9=D 8+n+1 → CopyRows start out → ∀ a b c,a   ≤   r → a+b   ≤   n → a+c   ≤   n →
    ∃ t,t   ≤   128*(a+1)*(P+1) ∧ Path P t (node start (D 0) (triple T D a b c))
      (node out (D 0) (triple T D 0 (a+b) (a+c))) := by run_tac checkedFrom `FullBodyClosure.Copy "copy_run"
private theorem transfer_run : ∀ {D T P j k wj wk start out},Grid D T → D 12   ≤   P → j < 12 → k < 12 → j≠k →
    D (j+1)=D j+wj+1 → D (k+1)=D k+wk+1 → TransferRows j k start out →
    ∀ a b,a   ≤   wj → a+b   ≤   wk → ∃ t,t   ≤   128*(a+1)*(P+1) ∧ Path P t
      (node start (D 0) (Twin T D j k a b)) (node out (D 0) (Twin T D j k 0 (a+b))) := by run_tac checkedFrom `FullBodyClosure.Transfer "transfer_run"
private theorem counter_grid : ∀ {D T},Grid D T → ∀ j v,j < 12 → Grid D (counter T D j v) := by run_tac checkedFrom `FullBodyClosure.Index "counter_grid"
private theorem counter_other : ∀ {D T j k v w},Grid D T → j < 12 → k < 12 → j≠k → Unary D T j v →
  Unary D (counter T D k w) j v := by run_tac checkedFrom `FullBodyClosure.Copy "counter_other"
private theorem grid_mono : ∀ {D T},Grid D T → ∀ a b,a   ≤   b → b   ≤   12 → D a   ≤   D b := by run_tac checkedKernel "Grid.mono"
private def st (q : Nat) : Fin 7500 := ⟨q%7500,Nat.mod_lt _ (by decide)⟩
private def copyState (m : Fin 3) : Fin 7500 := st (#[2283,4899,7000][m.val]!)
private def restoreState (m : Fin 3) : Fin 7500 := st (#[2301,4915,7016][m.val]!)
private def readIndexState (m : Fin 3) : Fin 7500 := st (#[2682,5069,7136][m.val]!)
private theorem copy_actual (m : Fin 3) : CopyRows (copyState m) (restoreState m) := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.InputRows0 "copyCode0"
  · run_tac checkedFrom `FullBodyClosure.InputRows1 "copyCode1"
  · run_tac checkedFrom `FullBodyClosure.InputRows2 "copyCode2"
private theorem restore_actual (m : Fin 3) : TransferRows 1 2 (restoreState m) (readIndexState m) := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.InputRows0 "restoreEllCode0"
  · run_tac checkedFrom `FullBodyClosure.InputRows1 "restoreEllCode1"
  · run_tac checkedFrom `FullBodyClosure.InputRows2 "restoreEllCode2"
private theorem counter_fixed {D T j v} (unary : Unary D T j v) : counter T D j v=T := by
  funext i
  change (if D j < i ∧ i < D (j+1) then some (decide (i-D j   ≤   v)) else T i)=T i
  by_cases inside : D j < i ∧ i < D (j+1)
  · rw [if_pos inside];exact (unary i inside.1 inside.2).symm
  · rw [if_neg inside]
private theorem counter_commute {D T j k v w} (mono : ∀ a b,a   ≤   b → b   ≤   12 → D a   ≤   D b)
    (hj : j < 12) (hk : k < 12) (ne : j≠k) :
    counter (counter T D j v) D k w=counter (counter T D k w) D j v := by
  funext i
  change (if D k < i ∧ i < D (k+1) then some (decide (i-D k   ≤   w)) else
    if D j < i ∧ i < D (j+1) then some (decide (i-D j   ≤   v)) else T i)=
    (if D j < i ∧ i < D (j+1) then some (decide (i-D j   ≤   v)) else
      if D k < i ∧ i < D (k+1) then some (decide (i-D k   ≤   w)) else T i)
  by_cases a : D j < i ∧ i < D (j+1)
  · have b : ¬(D k < i ∧ i < D (k+1)) := by
      by_cases h : j < k
      · have :=mono (j+1) k (by omega) (by omega);omega
      · have :=mono (k+1) j (by omega) (by omega);omega
    simp only [if_neg b,if_pos a]
  · simp only [if_neg a]
/-- Connected actual copy-elln AND restoration phase, not an unpriced logical copy. -/
private theorem copy_restore {D T P n r ell} (m : Fin 3) (grid : Grid D T) (fit : D 12   ≤   P)
    (len1 : D 2=D 1+n+1) (len2 : D 3=D 2+r+1) (len8 : D 9=D 8+n+1)
    (small : ell   ≤   n) (bound : ell   ≤   r) (u2 : Unary D T 2 ell) (u1 : Unary D T 1 0) (u8 : Unary D T 8 0) :
    ∃ t,t   ≤   256*(ell+1)*(P+1) ∧
      Path P t (node (copyState m) (D 0) T) (node (readIndexState m) (D 0) (counter T D 8 ell)) := by
  obtain ⟨t,price,first⟩:=copy_run grid fit len2 len1 len8 (copy_actual m) ell 0 0 bound (by omega) (by omega)
  have init : triple T D ell 0 0=T := by
    change counter (counter (counter T D 2 ell) D 1 0) D 8 0=T
    rw [counter_fixed u2,counter_fixed u1,counter_fixed u8]
  rw [init] at first
  simp only [Nat.add_zero] at first
  let U:=counter T D 8 ell
  have gU : Grid D U:=counter_grid grid 8 ell (by decide)
  obtain ⟨s,price',last⟩:=transfer_run gU fit (by decide : 1 < 12) (by decide : 2 < 12) (by decide) len1 len2
    (restore_actual m) ell 0 small (by omega)
  simp only [Nat.add_zero] at last
  have mono:=grid_mono grid
  have same : Twin U D 1 2 ell 0=triple T D 0 ell ell := by
    change counter (counter (counter T D 8 ell) D 1 ell) D 2 0=
      counter (counter (counter T D 2 0) D 1 ell) D 8 ell
    rw [counter_commute (j:=8) (k:=1) mono (by decide) (by decide) (by decide)]
    rw [counter_commute (j:=8) (k:=2) mono (by decide) (by decide) (by decide)]
    rw [counter_commute (j:=1) (k:=2) mono (by decide) (by decide) (by decide)]
  rw [same] at last
  have final : Twin U D 1 2 0 ell=U := by
    change counter (counter U D 1 0) D 2 ell=U
    have un1 : Unary D U 1 0:=counter_other grid (by decide) (by decide) (by decide) u1
    have un2 : Unary D U 2 ell:=counter_other grid (by decide) (by decide) (by decide) u2
    rw [counter_fixed un1,counter_fixed un2]
  rw [final] at last
  have path:=first.append last
  refine ⟨_,?_,path⟩
  nlinarith
private abbrev RouteR : Nat → Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "RouteR"
private abbrev RouteL : Nat → Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "RouteL"
private theorem keep : ∀ {P : Nat} (s q : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (mv : Move),
  h  ≤  P → h'  ≤  P → 4  ≤  s.val → SerializedBody.machine.step s (T h)=(q,T h,mv) →
  (match mv with | .left=>h-1 | .stay=>h | .right=>h+1)=h' →
  Path P 1 (node s h T) (node q h' T) := by run_tac checkedKernel "keep"
private theorem goR : ∀ {D T i j s q P},Grid D T → RouteR i j s q → j  ≤  12 → D 12  ≤  P →
  Path P (D j-D i+(j-i)) (node s (D i) T) (node q (D j) T) := by run_tac checkedKernel "Grid.goR"
private theorem goL : ∀ {D T i j s q P},Grid D T → RouteL i j s q → i  ≤  12 → D 12  ≤  P →
  Path P (D i-D j+(i-j)) (node s (D i) T) (node q (D j) T) := by run_tac checkedKernel "Grid.goL"
private theorem grid_blank : ∀ {D T},Grid D T → ∀ j,j  ≤  12 → T (D j)=none := by run_tac checkedKernel "Grid.blank"
private theorem grid_rise : ∀ {D T},Grid D T → ∀ j,j < 12 → D j < D (j+1) := by run_tac checkedKernel "Grid.rise"
private abbrev foldState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "foldState"
private abbrev hornerState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "hornerState"
private abbrev lookupState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Beta "lookupState"
private abbrev lookupLoopState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Beta "lookupLoopState"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Return "returnState"
private abbrev ToHRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "ToHRows"
private abbrev FromHRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "FromHRows"
private abbrev PopBufferRows : Fin 7500 → Fin 7500 → (Bool → Fin 7500) → Prop := by run_tac checkedFrom `FullBodyClosure.Buffer "PopBufferRows"
private abbrev BetaLiftRows : Fin 7500 → (Bool → Fin 7500) → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "BetaLiftRows"
private abbrev LookupRows : Fin 3 → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "LookupRows"
private def foldRoute (m : Fin 3) : Fin 7500 := st (#[2762,5149,7216][m.val]!)
private theorem fold_jump (m : Fin 3) : SerializedBody.machine.step (foldState m) none=(foldRoute m,none,.stay) := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.InputRows0 "foldJump0"
  · run_tac checkedFrom `FullBodyClosure.InputRows1 "foldJump1"
  · run_tac checkedFrom `FullBodyClosure.InputRows2 "foldJump2"
private theorem pop_buffer_actual (m : Fin 3) : PopBufferRows (foldRoute m) (lookupState m) (hornerState m) := by
  fin_cases m
  · run_tac checkedFrom `FullBodyClosure.BufferRows "popBufferCode0"
  · run_tac checkedFrom `FullBodyClosure.BufferRows "popBufferCode1"
  · run_tac checkedFrom `FullBodyClosure.BufferRows "popBufferCode2"
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
private theorem fold_safe (m : Fin 3) : 4  ≤  (foldState m).val := by fin_cases m <;> decide
private theorem fold_empty {D T P} (m : Fin 3) (grid : Grid D T) (room : D 12  ≤  P)
    (stop : T (D 9+1)≠some true) :
    ∃ t,t  ≤  32*(P+1) ∧ Path P t (node (foldState m) (D 0) T) (node (lookupState m) (D 0) T) := by
  obtain ⟨enter,scan,skip,take,flag,back,ret,empty,se,ss,sk,st,safe,forward,emptyRoute,reverse,
    entry,rs,rk,rn,emptyRow,reads⟩:=pop_buffer_actual m
  have rootFit : D 0  ≤  P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
  have bank10:=grid_mono grid 10 12 (by decide) (by decide)
  have rise9:=grid_rise grid 9 (by decide)
  change D 9 < D 10 at rise9
  have order:=grid_mono grid 0 9 (by decide) (by decide)
  have one:=keep (foldState m) (foldRoute m) (D 0) (D 0) T .stay (P:=P) rootFit rootFit (fold_safe m)
    (by rw [grid_blank grid 0 (by decide)];exact fold_jump m) rfl
  have route:=goR grid forward (by decide) room
  have two:=keep enter scan (D 9) (D 9+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [grid_blank grid 9 (by decide)];exact entry) rfl
  have three:=keep scan take (D 9+1) (D 9) T .left (P:=P) (by omega) (by omega) ss (rn _ stop) rfl
  have four:=keep take empty (D 9) (D 9) T .stay (P:=P) (by omega) (by omega) st
    (by rw [grid_blank grid 9 (by decide)];exact emptyRow) rfl
  have tail:=goL grid emptyRoute (by decide) room
  have path:=one.append (route.append (two.append (three.append (four.append tail))))
  refine ⟨_,?_,path⟩
  omega
/-- Complete empty-buffer fold exit AND physical beta lookup, arbitrary actual unary index. -/
private theorem fold_empty_lookup {D T P H Q F n} (m : Fin 3) (grid : Grid D T)
    (before : H  ≤  D 0) (d0 : D 0=F+1) (room : D 12  ≤  P) (len : D 2=D 1+n+1)
    (positive : 0 < Q) (arena : H+Q < F) (hn : n < H) (header : T H=none) (fence : T F=some false)
    (marks : ∀ i,H < i → i  ≤  H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (beta : Fin n → Bool) (cells : ∀ j : Fin n,T (H-1-j.val)=some (beta j))
    (index : Fin n) (unary : Unary D T 1 index.val) (stop : T (D 9+1)≠some true) :
    ∃ t,t  ≤  512*(n+1)*(P+1) ∧ Path P t (node (foldState m) (D 0) T)
      (node (returnState m (beta index)) (D 0) (counter T D 1 0)) := by
  obtain ⟨s,price,first⟩:=fold_empty m grid room stop
  obtain ⟨t,price',last⟩:=beta_lookup m grid before d0 room len positive arena hn header fence marks gap
    beta cells index (beta_lift_actual m) (beta_loop_actual m)
  rw [counter_fixed unary] at last
  have path:=first.append last
  refine ⟨_,?_,path⟩
  nlinarith
private theorem grid_make : ∀ {D T},(∀ j,j < 12 → D j < D (j+1)) →
    (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) → (∀ j,j ≤ 12 → T (D j)=none) →
    (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) → Grid D T := by run_tac checkedKernel "Grid.mk"
private theorem grid_cells : ∀ {D T},Grid D T → ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b := by run_tac checkedKernel "Grid.cells"
private theorem Context.grid {D T S L H Q F r M W n source beta} (ctx : Context D T S L H Q F r M W n source beta) : Grid D T :=
  grid_make ctx.rise ctx.mono ctx.blank ctx.cells
/-- Only a proof-frame transport for an already established tape; not a machine instruction. -/
private theorem Context.withWorkspace {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (U : Nat → Option Bool)
    (low : ∀ i,i < D 0 → U i=T i) (blank : ∀ j,j ≤ 12 → U (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,U i=some b) :
    Context D U S L H Q F r M W n source beta := by
  have hH : H < D 0 := by have :=ctx.positive;have :=ctx.arena;have :=ctx.anchor;omega
  refine ⟨ctx.sl,ctx.lh,ctx.width,ctx.positive,ctx.arena,ctx.anchor,ctx.rise,ctx.mono,blank,cells,
    ctx.len4,ctx.len11,ctx.window,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [low S ctx.before];exact ctx.eof
  · rw [low L (by have :=ctx.lh;omega)];exact ctx.left
  · rw [low H hH];exact ctx.right
  · rw [low F (by have :=ctx.anchor;omega)];exact ctx.fence
  · intro i lo hi;rw [low i (by have :=ctx.lh;omega)];exact ctx.reg i lo hi
  · intro i lo hi;rw [low i (by omega)];exact ctx.ass i lo hi
  · intro j;rw [low (H-1-j.val) (by omega)];exact ctx.betaCells j
  · intro i lo hi;rw [low i (by have :=ctx.arena;have :=ctx.anchor;omega)];exact ctx.marks i lo hi
  · intro i lo hi;rw [low i (by have :=ctx.anchor;omega)];exact ctx.gap i lo hi
  · intro i lo hi;rw [low i (by have :=ctx.before;omega)];exact ctx.sourceCells i lo hi
private theorem Context.withCounter {D T S L H Q F r M W n source beta}
    (ctx : Context D T S L H Q F r M W n source beta) (j v : Nat) (hj : j < 12) :
    Context D (counter T D j v) S L H Q F r M W n source beta := by
  have g:=counter_grid ctx.grid j v hj
  apply ctx.withWorkspace (counter T D j v)
  · intro i hi
    change (if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else T i)=T i
    have :=ctx.mono 0 j (by omega) (by omega)
    exact if_neg (by omega)
  · exact grid_blank g
  · exact grid_cells g
end FullBodyClosure
