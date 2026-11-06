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

private theorem separate_fields {D T j k i} (g : Grid D T) (hj : j < 12) (hk : k < 12) (different : j≠k)
    (lo : D j < i) (hi : i < D (j+1)) : ¬(D k < i ∧ i < D (k+1)) := by
  by_cases h : j < k
  · have :=grid_mono g (j+1) k (by omega) (by omega);omega
  · have :=grid_mono g (k+1) j (by omega) (by omega);omega
private theorem counter_other {D T j k v w} (g : Grid D T) (hj : j < 12) (hk : k < 12) (different : j≠k)
    (old : Unary D T j v) : Unary D (counter T D k w) j v := by
  intro i lo hi
  change (if D k < i ∧ i < D (k+1) then some (decide (i-D k≤w)) else T i)=_
  rw [if_neg (separate_fields g hj hk different lo hi)]
  exact old i lo hi
private def triple (T : Nat → Option Bool) (D : Nat → Nat) (a b c : Nat) : Nat → Option Bool :=
  counter (counter (counter T D 2 a) D 1 b) D 8 c
private theorem triple_grid {T D} (g : Grid D T) (a b c : Nat) : Grid D (triple T D a b c) :=
  counter_grid (counter_grid (counter_grid g 2 a (by decide)) 1 b (by decide)) 8 c (by decide)
private theorem triple_two {T D} (g : Grid D T) (a b c : Nat) : Unary D (triple T D a b c) 2 a := by
  exact counter_other (counter_grid (counter_grid g 2 a (by decide)) 1 b (by decide))
    (by decide) (by decide) (by decide) (counter_other (counter_grid g 2 a (by decide))
      (by decide) (by decide) (by decide) (counter_unary T D 2 a))
private theorem triple_one {T D} (g : Grid D T) (a b c : Nat) : Unary D (triple T D a b c) 1 b := by
  exact counter_other (counter_grid (counter_grid g 2 a (by decide)) 1 b (by decide))
    (by decide) (by decide) (by decide) (counter_unary (counter T D 2 a) D 1 b)
private theorem triple_eight (T : Nat → Option Bool) (D : Nat → Nat) (a b c : Nat) :
    Unary D (triple T D a b c) 8 c:=counter_unary (counter (counter T D 2 a) D 1 b) D 8 c
private theorem triple_down_two {T D a b c r} (g : Grid D T) (len : D 3=D 2+r+1)
    (pos : 0 < a) (small : a≤r) : put (triple T D a b c) (D 2+a) (some false)=triple T D (a-1) b c := by
  have inside : D 2 < D 2+a ∧ D 2+a < D 3 := by omega
  have n8:=separate_fields g (by decide : 2 < 12) (by decide : 8 < 12) (by decide) inside.1 inside.2
  have n1:=separate_fields g (by decide : 2 < 12) (by decide : 1 < 12) (by decide) inside.1 inside.2
  rw [triple,counter_put_outside _ D 8 c _ _ n8,counter_put_outside _ D 1 b _ _ n1,
    counter_down T D 2 a r len pos small]
  rfl
private theorem triple_up_one {T D a b c n} (g : Grid D T) (len : D 2=D 1+n+1) (small : b < n) :
    put (triple T D a b c) (D 1+b+1) (some true)=triple T D a (b+1) c := by
  have inside : D 1 < D 1+b+1 ∧ D 1+b+1 < D 2 := by omega
  have n8:=separate_fields g (by decide : 1 < 12) (by decide : 8 < 12) (by decide) inside.1 inside.2
  rw [triple,counter_put_outside _ D 8 c _ _ n8,counter_up _ D 1 b n len small]
  rfl
private theorem triple_up_eight {T D a b c n} (len : D 9=D 8+n+1) (small : c < n) :
    put (triple T D a b c) (D 8+c+1) (some true)=triple T D a b (c+1) := by
  exact counter_up _ D 8 c n len small
private def CopyRows (start out : Fin 7500) : Prop :=
  ∃ dec incOne incEight : Fin 7500,4≤start.val ∧
    SerializedBody.machine.step start none=(dec,none,.stay) ∧
    DecRows 2 dec out incOne ∧ IncRows 1 incOne incEight ∧ IncRows 8 incEight start
private theorem copy_price (P a t d i j : Nat)
    (hd : d≤4*P+20) (hi : i≤4*P+20) (hj : j≤4*P+20)
    (ht : t≤128*(a+1)*(P+1)) :
    1+d+i+j+t≤128*(a+2)*(P+1) := by nlinarith
private theorem copy_run {D T P r n start out} (grid : Grid D T) (fit : D 12≤P)
    (len2 : D 3=D 2+r+1) (len1 : D 2=D 1+n+1) (len8 : D 9=D 8+n+1)
    (code : CopyRows start out) :
    ∀ a b c,a≤r → a+b≤n → a+c≤n →
      ∃ t,t≤128*(a+1)*(P+1) ∧ Path P t (node start (D 0) (triple T D a b c))
        (node out (D 0) (triple T D 0 (a+b) (a+c))) := by
  rcases code with ⟨dec,incOne,incEight,ss,jump,decrement,incrementOne,incrementEight⟩
  have rootFit : D 0≤P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) fit
  have order1:=grid_mono grid 0 1 (by decide) (by decide)
  have order2:=grid_mono grid 0 2 (by decide) (by decide)
  have order8:=grid_mono grid 0 8 (by decide) (by decide)
  have bank9:=grid_mono grid 9 12 (by decide) (by decide)
  have bank3:=grid_mono grid 3 12 (by decide) (by decide)
  have order28:=grid_mono grid 2 8 (by decide) (by decide)
  intro a
  induction a with
  | zero =>
    intro b c ha hb hc
    have g:=triple_grid grid 0 b c
    have one:=keep start dec (D 0) (D 0) (triple T D 0 b c) .stay (P:=P) rootFit rootFit ss
      (by rw [grid_blank g 0 (by decide)];exact jump) rfl
    have last:=dec_zero g (by decide) fit len2 (triple_two grid 0 b c) decrement
    have path:=one.append last
    simp only [Nat.zero_add]
    refine ⟨_,?_,path⟩
    omega
  | succ a ih =>
    intro b c ha hb hc
    have g:=triple_grid grid (a+1) b c
    have one:=keep start dec (D 0) (D 0) (triple T D (a+1) b c) .stay (P:=P) rootFit rootFit ss
      (by rw [grid_blank g 0 (by decide)];exact jump) rfl
    have down:=dec_positive g (by decide) fit len2 (triple_two grid (a+1) b c) (by omega) ha decrement
    rw [triple_down_two grid len2 (by omega) ha] at down
    simp only [Nat.add_sub_cancel] at down
    have up1:=inc_success (triple_grid grid a b c) (by decide) fit len1 (triple_one grid a b c) (by omega) incrementOne
    rw [triple_up_one grid len1 (by omega)] at up1
    have up8:=inc_success (triple_grid grid a (b+1) c) (by decide) fit len8 (triple_eight T D a (b+1) c) (by omega) incrementEight
    rw [triple_up_eight len8 (by omega)] at up8
    obtain ⟨t,price,tail⟩:=ih (b+1) (c+1) (by omega) (by omega) (by omega)
    have path:=one.append (down.append (up1.append (up8.append tail)))
    rw [show a+(b+1)=(a+1)+b by omega,show a+(c+1)=(a+1)+c by omega] at path
    refine ⟨_,?_,path⟩
    have hd : 2*(D 2-D 0+2)+2*(a+1)+4≤4*P+20 := by omega
    have hi : 2*(D 1-D 0+1)+2*b+4≤4*P+20 := by omega
    have hj : 2*(D 8-D 0+8)+2*c+4≤4*P+20 := by omega
    have total:=copy_price P a t _ _ _ hd hi hj price
    simpa only [Nat.add_assoc] using total
end FullBodyClosure
