import FullBodyClosure.Index
namespace FullBodyClosure
open Lean Elab Tactic in
private def checkedKernel (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name := (leaf.splitOn ".").foldl Lean.Name.str
    (Lean.Name.str (Lean.Name.num `_private.SerializedBodyCompletion.Kernel 0) "SerializedBodyCompletion")
  let some ci := env.find? name | throwError "Missing exact immutable declaration: {name}"
  let some owner := env.getModuleIdxFor? name | throwError "Missing immutable owner: {name}"
  unless owner.toNat < env.header.moduleNames.size do throwError "Owner index outside imported header"
  unless env.header.moduleNames[owner]! == `SerializedBodyCompletion.Kernel do
    throwError "Wrong immutable owner: {name}"
  logInfo m!"kernel-adapter|{name}|{ci.type}"
  closeMainGoal `checkedKernel (mkConst name (ci.levelParams.map Level.param))
private abbrev Node : Type := by run_tac checkedKernel "Node"
private abbrev Path : Nat → Nat → Node → Node → Prop := by run_tac checkedKernel "Path"
private abbrev Grid : (Nat → Nat) → (Nat → Option Bool) → Prop := by run_tac checkedKernel "Grid"
private abbrev RouteR : Nat → Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "RouteR"
private abbrev RouteL : Nat → Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "RouteL"
private abbrev Unary : (Nat → Nat) → (Nat → Option Bool) → Nat → Nat → Prop := by run_tac checkedKernel "Unary"
private abbrev DecRows : Nat → Fin 7500 → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "DecRows"
private abbrev IncRows : Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "IncRows"
open Pnp3.Complexity.Uniform.V1
private abbrev node : Fin 7500 → Nat → (Nat → Option Bool) → Node := by run_tac checkedKernel "Node.mk"
private abbrev nodeHead : Node → Nat := by run_tac checkedKernel "Node.head"
private abbrev put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by run_tac checkedKernel "put"
private abbrev embed : ∀ {N B : Nat} (c : Node), (nodeHead c) < tapeLength N B → Config 7500 N B := by run_tac checkedKernel "embed"
private abbrev dest : Nat → Move → Nat := by run_tac checkedKernel "dest"
private abbrev paint : (Nat → Option Bool) → Nat → Nat → Bool → Nat → Option Bool := by run_tac checkedKernel "paint"
private abbrev ToHRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "ToHRows"
private abbrev FromHRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "FromHRows"
private abbrev ClearRows : Nat → Bool → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "ClearRows"
private abbrev RestoreRows : Bool → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "RestoreRows"
private theorem Path.bounds : ∀ {P t c d} (_h : Path P t c d),
    (nodeHead c) ≤ P ∧ (nodeHead d) ≤ P := by run_tac checkedKernel "Path.bounds"
private theorem Path.append : ∀ {P t u c d e} (_h : Path P t c d) (_g : Path P u d e),
    Path P (t+u) c e := by run_tac checkedKernel "Path.append"
private theorem Path.execute : ∀ {N B P t c d} (h : Path P t c d) (hp : P < tapeLength N B),
    SerializedBody.machine.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by run_tac checkedKernel "Path.execute"
private theorem Path.prefix : ∀ {P t c d} (path : Path P t c d) {N B : Nat}
    (fit : P < tapeLength N B),
    ∀ u,u < t →
    (SerializedBody.machine.run u (embed c (lt_of_le_of_lt path.bounds.1 fit))).state.val ≥ 4 := by run_tac checkedKernel "Path.prefix"
private theorem hop : ∀ {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (_hb : h ≤ P) (_ha : h' ≤ P)
    (_safe : 4 ≤ s.val)
    (_row : SerializedBody.machine.step s (T h) = (s',b,m)) (_hm : dest h m = h'),
    Path P 1 (node (s) (h) (T)) (node (s') (h') (put T h b)) := by run_tac checkedKernel "hop"
private theorem put_same : ∀ (T : Nat → Option Bool) (h : Nat),
    put T h (T h) = T := by run_tac checkedKernel "put_same"
private theorem keep : ∀ {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (_hb : h ≤ P) (_ha : h' ≤ P)
    (_safe : 4 ≤ s.val)
    (_row : SerializedBody.machine.step s (T h) = (s',T h,m)) (_hm : dest h m=h'),
    Path P 1 (node (s) (h) (T)) (node (s') (h') (T)) := by run_tac checkedKernel "keep"
private theorem sweepR : ∀ {P : Nat} (s : Fin 7500) (T : Nat → Option Bool) (h r : Nat) (_fit : h+r ≤ P) (_safe : 4 ≤ s.val) (_rows : ∀ i, h ≤ i → i < h+r → SerializedBody.machine.step s (T i)=(s,T i,.right)),
    Path P r (node (s) (h) (T)) (node (s) (h+r) (T)) := by run_tac checkedKernel "sweepR"
private theorem sweepL : ∀ {P : Nat} (s : Fin 7500) (T : Nat → Option Bool) (low r : Nat) (_fit : low+r ≤ P) (_safe : 4 ≤ s.val) (_rows : ∀ i, low < i → i ≤ low+r → SerializedBody.machine.step s (T i)=(s,T i,.left)),
    Path P r (node (s) (low+r) (T)) (node (s) (low) (T)) := by run_tac checkedKernel "sweepL"
private theorem crossR : ∀ {P : Nat} (e s q : Fin 7500) (T : Nat → Option Bool)
    (a w : Nat) (_fit : a+w+1 ≤ P) (_safeE : 4 ≤ e.val) (_safeS : 4 ≤ s.val)
    (_atA : T a=none) (_atB : T (a+w+1)=none)
    (_cells : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (_start : SerializedBody.machine.step e none=(s,none,.right))
    (_loop : ∀ b, SerializedBody.machine.step s (some b)=(s,some b,.right))
    (_stop : SerializedBody.machine.step s none=(q,none,.stay)),
    Path P (w+2) (node (e) (a) (T)) (node (q) (a+w+1) (T)) := by run_tac checkedKernel "crossR"
private theorem crossL : ∀ {P : Nat} (e s q : Fin 7500) (T : Nat → Option Bool)
    (a w : Nat) (_fit : a+w+1 ≤ P) (_safeE : 4 ≤ e.val) (_safeS : 4 ≤ s.val)
    (_atA : T a=none) (_atB : T (a+w+1)=none)
    (_cells : ∀ i, a < i → i < a+w+1 → ∃ b, T i=some b)
    (_start : SerializedBody.machine.step e none=(s,none,.left))
    (_loop : ∀ b, SerializedBody.machine.step s (some b)=(s,some b,.left))
    (_stop : SerializedBody.machine.step s none=(q,none,.stay)),
    Path P (w+2) (node (e) (a+w+1) (T)) (node (q) (a) (T)) := by run_tac checkedKernel "crossL"
private theorem Grid.change_some : ∀ {D T} (_g : Grid D T) (h : Nat) (b c : Bool)
    (_old : T h=some b),
    Grid D (put T h (some c)) := by run_tac checkedKernel "Grid.change_some"
private theorem Grid.goR : ∀ {D T i j s q P} (_g : Grid D T) (_r : RouteR i j s q)
    (_hj : j ≤ 12) (_fit : D 12 ≤ P),
    Path P (D j-D i+(j-i)) (node (s) (D i) (T)) (node (q) (D j) (T)) := by run_tac checkedKernel "Grid.goR"
private theorem Grid.goL : ∀ {D T i j s q P} (_g : Grid D T) (_r : RouteL i j s q)
    (_hi : i ≤ 12) (_fit : D 12 ≤ P),
    Path P (D i-D j+(i-j)) (node (s) (D i) (T)) (node (q) (D j) (T)) := by run_tac checkedKernel "Grid.goL"
private theorem Grid.painted : ∀ {D T} (_g : Grid D T) (j : Nat) (_hj : j < 12) (b : Bool),
    Grid D (paint T (D j+1) (D (j+1)-D j-1) b) := by run_tac checkedKernel "Grid.painted"
private theorem paint_zero : ∀ (T : Nat → Option Bool) (h : Nat) (b : Bool),
    paint T h 0 b=T := by run_tac checkedKernel "paint_zero"
private theorem paint_next : ∀ (T : Nat → Option Bool) (h w : Nat) (b : Bool),
    paint (put T h (some b)) (h+1) w b=paint T h (w+1) b := by run_tac checkedKernel "paint_next"
private theorem paint_outside : ∀ {T h w b i} (_outside : i < h ∨ h+w ≤ i),
    paint T h w b i=T i := by run_tac checkedKernel "paint_outside"
private theorem clear_run : ∀ {D T P j b start out} (_grid : Grid D T) (_hj : j < 12)
    (_fit : D 12 ≤ P) (_code : ClearRows j b start out),
    Path P (2*(D (j+1)-D 0+j)+2) (node (start) (D 0) (T))
      (node (out) (D 0) (paint T (D j+1) (D (j+1)-D j-1) b)) := by run_tac checkedKernel "clear_run"
private theorem restore_run : ∀ {S L H Q F P c T b entry out}
    (_sl : S < L) (_lh : L < H) (_physical : c < S)
    (_positive : 0 < Q) (_arena : H+Q < F) (_fit : F+1 ≤ P)
    (_ts : T S=none) (_tl : T L=none) (_th : T H=none)
    (_td : T (F+1)=none) (_tf : T F=some false) (_hole : T c=none)
    (_reg : ∀ i,S < i → i < L → ∃ v,T i=some v)
    (_ass : ∀ i,L < i → i < H → ∃ v,T i=some v)
    (_marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (_gap : ∀ i,H+Q < i → i < F → T i=none)
    (_src : ∀ i,c < i → i < S → ∃ v,T i=some v)
    (_rows : RestoreRows b entry out),
    Path P ((F+2-H)+(H-S+2)+(2*(S-c)+1)+(H-S+2)) (node (entry) (F+1) (T))
      (node (out) (H) (put T c (some b))) := by run_tac checkedKernel "restore_run"
private theorem to_H : ∀ {H Q F P T entry out} (_positive : 0 < Q) (_room : H+Q < F)
    (_fit : F+1 ≤ P) (_td : T (F+1)=none) (_tf : T F=some false) (_th : T H=none)
    (_marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (_gap : ∀ i,H+Q < i → i < F → T i=none) (_rows : ToHRows entry out),
    Path P (F+2-H) (node (entry) (F+1) (T)) (node (out) (H) (T)) := by run_tac checkedKernel "to_H"
private theorem from_H : ∀ {H Q F P T entry out} (_positive : 0 < Q) (_room : H+Q < F)
    (_fit : F+1 ≤ P) (_tf : T F=some false) (_th : T H=none)
    (_marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (_gap : ∀ i,H+Q < i → i < F → T i=none) (_rows : FromHRows entry out),
    Path P (F+1-H) (node (entry) (H) (T)) (node (out) (F+1) (T)) := by run_tac checkedKernel "from_H"
private theorem unary_true : ∀ {D T j v w} (_h : Unary D T j v)
    (_len : D (j+1)=D j+w+1) (_hv : v ≤ w) {i : Nat}
    (_lo : D j < i) (_hi : i ≤ D j+v),
    T i=some true := by run_tac checkedKernel "unary_true"
private theorem unary_boundary : ∀ {D T j v w} (_grid : Grid D T) (_h : Unary D T j v)
    (_hj : j < 12) (_len : D (j+1)=D j+w+1) (_hv : v ≤ w),
    T (D j+v+1)≠some true := by run_tac checkedKernel "unary_boundary"
private theorem dec_zero : ∀ {D T j w P start zero pos} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j 0) (_code : DecRows j start zero pos),
    Path P (2*(D j-D 0+j)+3) (node (start) (D 0) (T)) (node (zero) (D 0) (T)) := by run_tac checkedKernel "dec_zero"
private theorem dec_positive : ∀ {D T j w v P start zero pos} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j v) (_positive : 0 < v) (_small : v ≤ w)
    (_code : DecRows j start zero pos),
    Path P (2*(D j-D 0+j)+2*v+4) (node (start) (D 0) (T))
      (node (pos) (D 0) (put T (D j+v) (some false))) := by run_tac checkedKernel "dec_positive"
private theorem inc_success : ∀ {D T j w v P start out} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j v) (_small : v < w) (_code : IncRows j start out),
    Path P (2*(D j-D 0+j)+2*v+4) (node (start) (D 0) (T))
      (node (out) (D 0) (put T (D j+v+1) (some true))) := by run_tac checkedKernel "inc_success"
private theorem grid_mono : ∀ {D T}, Grid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by run_tac checkedKernel "Grid.mono"
private theorem grid_blank : ∀ {D T}, Grid D T → ∀ j,j ≤ 12 → T (D j)=none := by run_tac checkedKernel "Grid.blank"
private theorem grid_cells : ∀ {D T}, Grid D T → ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b := by run_tac checkedKernel "Grid.cells"
private theorem grid_rise : ∀ {D T}, Grid D T → ∀ j,j < 12 → D j < D (j+1) := by run_tac checkedKernel "Grid.rise"
private abbrev ClearPlan : List (Nat × Bool) → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "ClearPlan"
private abbrev scrub : (Nat → Nat) → List (Nat × Bool) → (Nat → Option Bool) → Nat → Option Bool := by run_tac checkedKernel "scrub"
private abbrev clearCost : (Nat → Nat) → List (Nat × Bool) → Nat := by run_tac checkedKernel "clearCost"
private theorem clear_plan : ∀ {D T P edits start out}, Grid D T → D 12 ≤ P → ClearPlan edits start out →
    Path P (clearCost D edits) (node start (D 0) T) (node out (D 0) (scrub D edits T)) ∧
      Grid D (scrub D edits T) ∧ ∀ i,i < D 0 → scrub D edits T i=T i := by run_tac checkedKernel "clear_plan"
private theorem clearCost_le : ∀ {D P edits}, (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) → D 12 ≤ P →
    (∀ jb ∈ edits,jb.1 < 12) → clearCost D edits ≤ edits.length*(2*P+24) := by run_tac checkedKernel "clearCost_le"
private theorem plan_nil : ∀ q,ClearPlan [] q q := by run_tac checkedKernel "ClearPlan.nil"
private theorem plan_cons : ∀ {j b xs q mid out}, j < 12 → ClearRows j b q mid → ClearPlan xs mid out → ClearPlan ((j,b)::xs) q out := by run_tac checkedKernel "ClearPlan.cons"
private theorem rnil : ∀ i q,RouteR i i q q := by run_tac checkedKernel "RouteR.nil"
private theorem lnil : ∀ i q,RouteL i i q q := by run_tac checkedKernel "RouteL.nil"
private theorem rnext : ∀ {i j e s q x}, 4 ≤ e.val → 4 ≤ s.val →
    SerializedBody.machine.step e none=(s,none,.right) →
    (∀ b,SerializedBody.machine.step s (some b)=(s,some b,.right)) →
    SerializedBody.machine.step s none=(q,none,.stay) → RouteR (i+1) j q x → RouteR i j e x := by run_tac checkedKernel "RouteR.next"
private theorem lnext : ∀ {i j e s q x}, 4 ≤ e.val → 4 ≤ s.val →
    SerializedBody.machine.step e none=(s,none,.left) →
    (∀ b,SerializedBody.machine.step s (some b)=(s,some b,.left)) →
    SerializedBody.machine.step s none=(q,none,.stay) → RouteL i j q x → RouteL (i+1) j e x := by run_tac checkedKernel "RouteL.next"
private theorem grid_make : ∀ {D T}, (∀ j,j < 12 → D j < D (j+1)) →
    (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) → (∀ j,j ≤ 12 → T (D j)=none) →
    (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) → Grid D T := by run_tac checkedKernel "Grid.mk"
open Lean Elab Tactic in
private def checkedFrom (owner : Name) (userNS leaf : String) : TacticM Unit := do
  let env ← getEnv
  let root:=Name.str (Name.num (Name.append `_private owner) 0) userNS
  let name:=(leaf.splitOn ".").foldl Name.str root
  let some ci:=env.find? name | throwError "Missing exact immutable declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing immutable module: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong owner for {name}"
  logInfo m!"row-adapter|{owner}|{name}|{ci.type}"
  closeMainGoal `checkedFrom (mkConst name (ci.levelParams.map Level.param))
private abbrev counter : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "counter"
private abbrev StrictIncRows : Nat → Fin 7500 → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "StrictIncRows"
private abbrev hornerState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "hornerState"
private abbrev transferState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "transferState"
private abbrev foldState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "foldState"
private abbrev HornerRows : Fin 3 → Bool → Prop := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "HornerRows"
private abbrev TransferRows : Fin 3 → Prop := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "TransferRows"
private theorem counter_grid : ∀ {D T} (_g : Grid D T) (j v : Nat) (_hj : j < 12),
    Grid D (counter T D j v) := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "counter_grid"
private theorem counter_unary : ∀ (T : Nat → Option Bool) (D : Nat → Nat) (j v : Nat),
    Unary D (counter T D j v) j v := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "counter_unary"
private theorem counter_down : ∀ (T : Nat → Option Bool) (D : Nat → Nat) (j v w : Nat)
    (_len : D (j+1)=D j+w+1) (_pos : 0 < v) (_fit : v ≤ w),
    put (counter T D j v) (D j+v) (some false)=counter T D j (v-1) := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "counter_down"
private theorem counter_up : ∀ (T : Nat → Option Bool) (D : Nat → Nat) (j v w : Nat)
    (_len : D (j+1)=D j+w+1) (_fit : v < w),
    put (counter T D j v) (D j+v+1) (some true)=counter T D j (v+1) := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "counter_up"
private theorem counter_put_outside : ∀ (T : Nat → Option Bool) (D : Nat → Nat) (j v h : Nat) (b : Option Bool)
    (_outside : ¬(D j < h ∧ h < D (j+1))),
    put (counter T D j v) h b=counter (put T h b) D j v := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "counter_put_outside"
private theorem strict_inc_success : ∀ {D T j w v P start out abort} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j v) (_small : v+1 < w) (_code : StrictIncRows j start out abort),
    Path P (2*(D j-D 0+j)+2*v+5) (node start (D 0) T)
      (node out (D 0) (put T (D j+v+1) (some true))) := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "strict_inc_success"
private theorem strict_inc_hits_cap : ∀ {D T j w v P start out abort} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j v) (_full : v+1=w) (_code : StrictIncRows j start out abort),
    Path P ((D j-D 0+j)+(v+3)+(D (j+1)-D 0+(j+1))) (node start (D 0) T)
      (node abort (D 0) (put T (D j+v+1) (some true))) := by run_tac checkedFrom `FullBodyClosure.Index "FullBodyClosure" "strict_inc_hits_cap"
private def ij (T : Nat → Option Bool) (D : Nat → Nat) (i j : Nat) : Nat → Option Bool :=
  counter (counter T D 8 j) D 1 i
private theorem ij_grid {D T} (g : Grid D T) (i j : Nat) : Grid D (ij T D i j) :=
  counter_grid (counter_grid g 8 j (by decide)) 1 i (by decide)
private theorem ij_unary1 (T : Nat → Option Bool) (D : Nat → Nat) (i j : Nat) : Unary D (ij T D i j) 1 i :=
  counter_unary (counter T D 8 j) D 1 i
private theorem ij_unary8 {D T} (g : Grid D T) (i j : Nat) : Unary D (ij T D i j) 8 j := by
  intro x lo hi
  have order : D 2 ≤ D 8:=grid_mono g 2 8 (by decide) (by decide)
  have outside : ¬(D 1 < x ∧ x < D 2) := by omega
  change (if D 1 < x ∧ x < D 2 then some (decide (x-D 1 ≤ i)) else counter T D 8 j x)=_
  rw [if_neg outside]
  exact counter_unary T D 8 j x lo hi
private theorem ij_down1 (T : Nat → Option Bool) (D : Nat → Nat) (i j n : Nat)
    (len : D 2=D 1+n+1) (pos : 0 < i) (fit : i ≤ n) :
    put (ij T D i j) (D 1+i) (some false)=ij T D (i-1) j :=
  counter_down (counter T D 8 j) D 1 i n len pos fit
private theorem ij_up1 (T : Nat → Option Bool) (D : Nat → Nat) (i j n : Nat)
    (len : D 2=D 1+n+1) (fit : i < n) :
    put (ij T D i j) (D 1+i+1) (some true)=ij T D (i+1) j :=
  counter_up (counter T D 8 j) D 1 i n len fit
private theorem ij_down8 {D T} (g : Grid D T) (i j n : Nat)
    (len : D 9=D 8+n+1) (pos : 0 < j) (fit : j ≤ n) :
    put (ij T D i j) (D 8+j) (some false)=ij T D i (j-1) := by
  have order : D 2 ≤ D 8:=grid_mono g 2 8 (by decide) (by decide)
  have out : ¬(D 1 < D 8+j ∧ D 8+j < D 2) := by omega
  change put (counter (counter T D 8 j) D 1 i) (D 8+j) (some false)=_
  rw [counter_put_outside _ _ _ _ _ _ out,counter_down T D 8 j n len pos fit]
  rfl
private theorem ij_up8 {D T} (g : Grid D T) (i j n : Nat)
    (len : D 9=D 8+n+1) (fit : j < n) :
    put (ij T D i j) (D 8+j+1) (some true)=ij T D i (j+1) := by
  have order : D 2 ≤ D 8:=grid_mono g 2 8 (by decide) (by decide)
  have out : ¬(D 1 < D 8+j+1 ∧ D 8+j+1 < D 2) := by omega
  change put (counter (counter T D 8 j) D 1 i) (D 8+j+1) (some true)=_
  rw [counter_put_outside _ _ _ _ _ _ out,counter_up T D 8 j n len fit]
  rfl
private theorem transfer_run {D T P n} (m : Fin 3) (g : Grid D T)
    (room : D 12 ≤ P) (len1 : D 2=D 1+n+1) (len8 : D 9=D 8+n+1)
    (code : TransferRows m) (i j : Nat) (small : i+j < n) :
    ∃ t,t ≤ 128*(j+1)*(P+1) ∧ Path P t (node (transferState m) (D 0) (ij T D i j))
      (node (foldState m) (D 0) (ij T D (i+j) 0)) := by
  rcases code with ⟨dec,inc,safe,jump,decCode,incCode⟩
  induction j generalizing i with
  | zero =>
    have grid:=ij_grid g i 0
    have root : D 0 ≤ P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
    have one:=keep (transferState m) dec (D 0) (D 0) (ij T D i 0) .stay (P:=P) root root safe
      (by rw [grid_blank grid 0 (by decide)];exact jump) rfl
    have back:=dec_zero grid (j:=8) (by decide) room len8 (ij_unary8 g i 0) decCode
    have total:=one.append back
    refine ⟨1+(2*(D 8-D 0+8)+3),?_,?_⟩
    · have :=grid_mono g 8 12 (by decide) (by decide);omega
    · exact total
  | succ j ih =>
    have grid:=ij_grid g i (j+1)
    have root : D 0 ≤ P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
    have one:=keep (transferState m) dec (D 0) (D 0) (ij T D i (j+1)) .stay (P:=P) root root safe
      (by rw [grid_blank grid 0 (by decide)];exact jump) rfl
    have down:=dec_positive grid (j:=8) (by decide) room len8 (ij_unary8 g i (j+1)) (by omega) (by omega) decCode
    rw [ij_down8 g i (j+1) n len8 (by omega) (by omega)] at down
    simp only [Nat.add_sub_cancel] at down
    have up:=inc_success (ij_grid g i j) (j:=1) (by decide) room len1 (ij_unary1 T D i j) (by omega) incCode
    rw [ij_up1 T D i j n len1 (by omega)] at up
    obtain ⟨t,price,rest⟩:=ih (i+1) (by omega)
    have total:=one.append (down.append (up.append rest))
    refine ⟨1+((2*(D 8-D 0+8)+2*(j+1)+4)+((2*(D 1-D 0+1)+2*i+4)+t)),?_,?_⟩
    · have d1 : D 1 ≤ P:=le_trans (grid_mono g 1 12 (by decide) (by decide)) room
      have d8 : D 8 ≤ P:=le_trans (grid_mono g 8 12 (by decide) (by decide)) room
      have jBound : j+1 ≤ P := by have :=grid_rise g 8 (by decide);have :=grid_mono g 9 12 (by decide) (by decide);omega
      have iBound : i ≤ P := by have :=grid_rise g 1 (by decide);have :=grid_mono g 2 12 (by decide) (by decide);omega
      have added : 1+(2*(D 8-D 0+8)+2*(j+1)+4)+(2*(D 1-D 0+1)+2*i+4) ≤ 128*(P+1) := by omega
      nlinarith
    · have eq : i+1+j=i+(j+1) := by omega
      rw [eq] at total
      exact total
private def Costed (P limit : Nat) (a b : Node) : Prop := ∃ t,t ≤ limit ∧ Path P t a b
private theorem Costed.of_path {P t limit a b} (path : Path P t a b) (price : t ≤ limit) : Costed P limit a b := ⟨t,price,path⟩
private theorem Costed.chain {P t s a b c} (first : Costed P t a b) (second : Costed P s b c) : Costed P (t+s) a c := by
  obtain ⟨x,hx,px⟩:=first;obtain ⟨y,hy,py⟩:=second
  exact ⟨x+y,by omega,px.append py⟩
private theorem Costed.relax {P t s a b} (path : Costed P t a b) (bound : t ≤ s) : Costed P s a b := by
  obtain ⟨x,hx,px⟩:=path;exact ⟨x,by omega,px⟩
private theorem primitive_price (D : Nat → Nat) (P j v : Nat) (dj : D j ≤ P) (hj : j ≤ 12) (hv : v ≤ P) :
    2*(D j-D 0+j)+2*v+5 ≤ 32*(P+1) := by omega
private theorem base_false_price (P n j : Nat) (h : j < n) :
    64*(P+1)+128*(j+1)*(P+1) ≤ 512*(n+1)*(P+1) := by nlinarith
private theorem base_true_price (P n j : Nat) (h : j+1 < n) :
    64*(P+1)+(32*(P+1)+128*(j+1+1)*(P+1)) ≤ 512*(n+1)*(P+1) := by nlinarith
private theorem base_cap_price (P n : Nat) :
    64*(P+1)+64*(P+1) ≤ 512*(n+1)*(P+1) := by nlinarith
private theorem recursive_price (P i n : Nat) :
    (64*(P+1)+(32*(P+1)+32*(P+1)))+512*(i+n+1)*(P+1) ≤ 512*(i+1+n+1)*(P+1) := by nlinarith
private theorem second_cap_price (P i n : Nat) :
    64*(P+1)+(32*(P+1)+64*(P+1)) ≤ 512*(i+1+n+1)*(P+1) := by nlinarith
private theorem first_cap_price (P i n : Nat) :
    64*(P+1)+64*(P+1) ≤ 512*(i+1+n+1)*(P+1) := by nlinarith
-- Complete capped Horner consumes I by actual dec/strict-inc rows, then physically transfers J back.
private theorem horner_run {D T P n} (m : Fin 3) (b : Bool) (g : Grid D T)
    (room : D 12 ≤ P) (len1 : D 2=D 1+n+1) (len8 : D 9=D 8+n+1)
    (code : HornerRows m b) (transfer : TransferRows m) (i j : Nat) (iFit : i ≤ n) (jFit : j < n) :
    let value:=2*i+j+(if b then 1 else 0)
    if value < n then
      Costed P (512*(i+n+1)*(P+1)) (node (hornerState m b) (D 0) (ij T D i j)) (node (foldState m) (D 0) (ij T D value 0))
    else ∃ left,left ≤ i ∧ Costed P (512*(i+n+1)*(P+1))
      (node (hornerState m b) (D 0) (ij T D i j)) (node (SerializedBodyRefinement.getAbort m) (D 0) (ij T D left n)) := by
  dsimp only
  rcases code with ⟨dec,zeroBranch,first,second,safe,jump,decCode,inc1,inc2,lastCode⟩
  have d1 : D 1 ≤ P:=le_trans (grid_mono g 1 12 (by decide) (by decide)) room
  have d8 : D 8 ≤ P:=le_trans (grid_mono g 8 12 (by decide) (by decide)) room
  have nBound : n ≤ P := by have :=grid_mono g 2 12 (by decide) (by decide);omega
  have root : D 0 ≤ P:=le_trans (grid_mono g 0 12 (by decide) (by decide)) room
  induction i generalizing j with
  | zero =>
    simp only [Nat.mul_zero,Nat.zero_add]
    have grid:=ij_grid g 0 j
    have entry:=keep (hornerState m b) dec (D 0) (D 0) (ij T D 0 j) .stay (P:=P) root root safe
      (by rw [grid_blank grid 0 (by decide)];exact jump) rfl
    have down:=dec_zero grid (j:=1) (by decide) room len1 (ij_unary1 T D 0 j) decCode
    have opened:=Costed.of_path (entry.append down) (show 1+(2*(D 1-D 0+1)+3) ≤ 64*(P+1) by omega)
    cases b with
    | false =>
      change zeroBranch=transferState m at lastCode
      rw [lastCode] at opened
      rw [if_pos (by simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] using jFit)]
      obtain ⟨t,price,path⟩:=transfer_run m g room len1 len8 transfer 0 j (by simpa using jFit)
      simp only [Nat.zero_add] at path
      have joined:=opened.chain (show Costed P (128*(j+1)*(P+1)) _ _ from ⟨t,price,path⟩)
      exact joined.relax (base_false_price P n j jFit)
    | true =>
      change StrictIncRows 8 zeroBranch (transferState m) (SerializedBodyRefinement.getAbort m) at lastCode
      by_cases enough : j+1 < n
      · have up:=strict_inc_success grid (j:=8) (by decide) room len8 (ij_unary8 g 0 j) enough lastCode
        rw [ij_up8 g 0 j n len8 (by omega)] at up
        have paid:=Costed.of_path up (primitive_price D P 8 j d8 (by decide) (by omega))
        obtain ⟨t,price,path⟩:=transfer_run m g room len1 len8 transfer 0 (j+1) (by simpa using enough)
        simp only [Nat.zero_add] at path
        have joined:=opened.chain (paid.chain (show Costed P (128*(j+1+1)*(P+1)) _ _ from ⟨t,price,path⟩))
        rw [if_pos (by simpa only [Nat.mul_zero,Nat.zero_add] using enough)]
        exact joined.relax (base_true_price P n j enough)
      · have full : j+1=n := by omega
        have failed:=strict_inc_hits_cap grid (j:=8) (by decide) room len8 (ij_unary8 g 0 j) full lastCode
        rw [ij_up8 g 0 j n len8 jFit,full] at failed
        have tickBound : (D 8-D 0+8)+(j+3)+(D 9-D 0+(8+1)) ≤ 64*(P+1) := by
          have :=grid_mono g 9 12 (by decide) (by decide);omega
        have paid:=Costed.of_path failed tickBound
        have joined:=opened.chain paid
        rw [if_neg (by simpa only [Nat.mul_zero,Nat.zero_add] using enough)]
        exact ⟨0,by omega,joined.relax (base_cap_price P n)⟩
  | succ i ih =>
    have grid:=ij_grid g (i+1) j
    have entry:=keep (hornerState m b) dec (D 0) (D 0) (ij T D (i+1) j) .stay (P:=P) root root safe
      (by rw [grid_blank grid 0 (by decide)];exact jump) rfl
    have down:=dec_positive grid (j:=1) (by decide) room len1 (ij_unary1 T D (i+1) j) (by omega) iFit decCode
    rw [ij_down1 T D (i+1) j n len1 (by omega) iFit] at down
    simp only [Nat.add_sub_cancel] at down
    have opened:=Costed.of_path (entry.append down)
      (show 1+(2*(D 1-D 0+1)+2*(i+1)+4) ≤ 64*(P+1) by omega)
    by_cases enough1 : j+1 < n
    · have up1:=strict_inc_success (ij_grid g i j) (j:=8) (by decide) room len8 (ij_unary8 g i j) enough1 inc1
      rw [ij_up8 g i j n len8 jFit] at up1
      have p1:=Costed.of_path up1 (primitive_price D P 8 j d8 (by decide) (by omega))
      by_cases enough2 : j+2 < n
      · have up2:=strict_inc_success (ij_grid g i (j+1)) (j:=8) (by decide) room len8 (ij_unary8 g i (j+1)) (by omega) inc2
        rw [ij_up8 g i (j+1) n len8 enough1] at up2
        have p2:=Costed.of_path up2 (primitive_price D P 8 (j+1) d8 (by decide) (by omega))
        have prefixPath:=opened.chain (p1.chain p2)
        have recursive:=ih (j+2) (by omega) enough2
        have value : 2*i+(j+2)+(if b then 1 else 0)=2*(i+1)+j+(if b then 1 else 0) := by omega
        rw [value] at recursive
        by_cases accepted : 2*(i+1)+j+(if b then 1 else 0) < n
        · rw [if_pos accepted] at recursive ⊢
          have joined:=prefixPath.chain recursive
          exact joined.relax (recursive_price P i n)
        · rw [if_neg accepted] at recursive ⊢
          obtain ⟨left,le,path⟩:=recursive
          exact ⟨left,by omega,(prefixPath.chain path).relax (recursive_price P i n)⟩
      · have full : (j+1)+1=n := by omega
        have failed:=strict_inc_hits_cap (ij_grid g i (j+1)) (j:=8) (by decide) room len8 (ij_unary8 g i (j+1)) full inc2
        rw [ij_up8 g i (j+1) n len8 enough1,full] at failed
        have tickBound : (D 8-D 0+8)+(j+1+3)+(D 9-D 0+(8+1)) ≤ 64*(P+1) := by
          have :=grid_mono g 9 12 (by decide) (by decide);omega
        have joined:=opened.chain (p1.chain (Costed.of_path failed tickBound))
        rw [if_neg (by omega : ¬ 2*(i+1)+j+(if b then 1 else 0) < n)]
        exact ⟨i,by omega,joined.relax (second_cap_price P i n)⟩
    · have full : j+1=n := by omega
      have failed:=strict_inc_hits_cap (ij_grid g i j) (j:=8) (by decide) room len8 (ij_unary8 g i j) full inc1
      rw [ij_up8 g i j n len8 jFit,full] at failed
      have tickBound : (D 8-D 0+8)+(j+3)+(D 9-D 0+(8+1)) ≤ 64*(P+1) := by
        have :=grid_mono g 9 12 (by decide) (by decide);omega
      have joined:=opened.chain (Costed.of_path failed tickBound)
      rw [if_neg (by omega : ¬ 2*(i+1)+j+(if b then 1 else 0) < n)]
      exact ⟨i,by omega,joined.relax (first_cap_price P i n)⟩
end FullBodyClosure
