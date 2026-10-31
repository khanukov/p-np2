import FullBodyClosure.Support
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
private def checkedSupport (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name := (leaf.splitOn ".").foldl Lean.Name.str
    (Lean.Name.str (Lean.Name.num `_private.FullBodyClosure.Support 0) "FullBodyClosure")
  let some ci := env.find? name | throwError "Missing exact own immutable declaration: {name}"
  let some owner := env.getModuleIdxFor? name | throwError "Missing immutable owner: {name}"
  unless owner.toNat < env.header.moduleNames.size do throwError "Owner index outside imported header"
  unless env.header.moduleNames[owner]! == `FullBodyClosure.Support do throwError "Wrong owner"
  logInfo m!"own-adapter|{name}|{ci.type}"
  closeMainGoal `checkedSupport (mkConst name (ci.levelParams.map Level.param))
private abbrev st : Nat → Fin 7500 := by run_tac checkedSupport "st"
private abbrev StackRows : (Fin 7 → Fin 7500) → Fin 7500 → Prop := by run_tac checkedSupport "StackRows"
private theorem stack_scan : ∀ {D T P start enter q found d}, Grid D T →
    RouteR 0 10 start enter → 4 ≤ enter.val →
    SerializedBody.machine.step enter none=(q 0,none,.right) → StackRows q found →
    D 12 ≤ P → D 10+3*d+4 ≤ D 11 →
    (∀ j,j < d → ∃ a b c : Bool,(a && b && c)=false ∧
      T (D 10+1+3*j)=some a ∧ T (D 10+1+3*j+1)=some b ∧ T (D 10+1+3*j+2)=some c) →
    T (D 10+1+3*d)=some true → T (D 10+1+3*d+1)=some true → T (D 10+1+3*d+2)=some true →
    Path P (D 10-D 0+3*d+14) (node start (D 0) T) (node found (D 10+3*d+3) T) := by run_tac checkedSupport "stack_scan"
private def successEdits : List (Nat × Bool) := [(1,false),(8,false),(6,false),(9,false),(10,true)]
private theorem successEdits_bound : ∀ jb ∈ successEdits,jb.1 < 12 := by
  intro jb hj
  simp only [successEdits,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl <;> decide
private def returnState (m : Fin 3) (b : Bool) : Fin 7500 :=
  st (#[1884,4505,6612,2218,4834,6935][3*(if b then 1 else 0)+m.val]!)
private def ReturnRows (m : Fin 3) (b : Bool) : Prop :=
  ∃ scanStart scanEnter : Fin 7500, ∃ q : Fin 7 → Fin 7500,
    ∃ found retreat1 retreat2 last back cleanup restore : Fin 7500,
    4 ≤ (returnState m b).val ∧ 4 ≤ scanEnter.val ∧ 4 ≤ found.val ∧
    4 ≤ retreat1.val ∧ 4 ≤ retreat2.val ∧ 4 ≤ last.val ∧
    SerializedBody.machine.step (returnState m b) none=(scanStart,none,.stay) ∧
    RouteR 0 10 scanStart scanEnter ∧ StackRows q found ∧
    SerializedBody.machine.step scanEnter none=(q 0,none,.right) ∧
    (∀ x,SerializedBody.machine.step found x=(retreat1,x,.left)) ∧
    (∀ x,SerializedBody.machine.step retreat1 x=(retreat2,x,.left)) ∧
    (∀ x,SerializedBody.machine.step retreat2 x=(last,x,.left)) ∧
    SerializedBody.machine.step last none=(back,none,.stay) ∧
    RouteL 10 0 back cleanup ∧ ClearPlan successEdits cleanup restore ∧
    (if m.val=2 then ToHRows restore (SerializedBody.done b)
      else RestoreRows (decide (m.val=1)) restore (SerializedBody.done b))
private theorem return_empty_path (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F c P : Nat) (source : Fin S → Bool) (b : Bool)
    (grid : Grid D T) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (room : D 12 ≤ P) (stackRoom : D 10+4 ≤ D 11)
    (stack : ∀ i,D 10 < i → i < D 11 → T i=some true)
    (eof : T S=none) (left : T L=none) (right : T H=none) (fence : T F=some false)
    (hole : c < S → T c=none)
    (reg : ∀ i,S < i → i < L → ∃ v,T i=some v)
    (ass : ∀ i,L < i → i < H → ∃ v,T i=some v)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (src : ∀ i,c < i → i < S → ∃ v,T i=some v)
    (code : ReturnRows (SerializedBody.sourceMode source c) b) :
    let U:=scrub D successEdits T
    let V:=if c < S then put U c (some (Pnp4.Frontier.ContractExpansion.padRead source c)) else U
    ∃ t,t ≤ 512*(P+1) ∧ Path P t (node (returnState (SerializedBody.sourceMode source c) b) (D 0) T)
      (node (SerializedBody.done b) H V) := by
  dsimp only
  rcases code with ⟨scanStart,scanEnter,q,found,r1,r2,last,back,cleanup,restore,
    safe,safeEnter,safeFound,safe1,safe2,safeLast,start,route,rows,entry,retreat1,retreat2,retreat3,exit,backRoute,plan,restoreRows⟩
  have lower (j : Nat) (hj : j ≤ 12) : D 0 ≤ D j:=grid_mono grid 0 j (by omega) hj
  have top (j : Nat) (hj : j ≤ 12) : D j ≤ P:=le_trans (grid_mono grid j 12 hj (by omega)) room
  have initial:=keep (returnState (SerializedBody.sourceMode source c) b) scanStart (D 0) (D 0) T .stay
    (P:=P) (top 0 (by decide)) (top 0 (by decide)) safe (by rw [grid_blank grid 0 (by decide)];exact start) rfl
  have scan:=stack_scan (P:=P) (d:=0) grid route safeEnter entry rows room (by simpa using stackRoom)
    (by intro j hj;omega)
    (stack _ (by omega) (by omega)) (stack _ (by omega) (by omega)) (stack _ (by omega) (by omega))
  simp only [Nat.mul_zero,Nat.add_zero] at scan
  have one:=keep found r1 (D 10+3) (D 10+2) T .left (P:=P) (by have :=top 11 (by decide);omega) (by have :=top 11 (by decide);omega) safeFound
    (retreat1 _) (by change D 10+3-1=D 10+2;omega)
  have two:=keep r1 r2 (D 10+2) (D 10+1) T .left (P:=P) (by have :=top 11 (by decide);omega) (by have :=top 11 (by decide);omega) safe1
    (retreat2 _) (by change D 10+2-1=D 10+1;omega)
  have three:=keep r2 last (D 10+1) (D 10) T .left (P:=P) (by have :=top 11 (by decide);omega) (top 10 (by decide)) safe2
    (retreat3 _) (by change D 10+1-1=D 10;omega)
  have finish:=keep last back (D 10) (D 10) T .stay (P:=P) (top 10 (by decide)) (top 10 (by decide)) safeLast
    (by rw [grid_blank grid 10 (by decide)];exact exit) rfl
  have returnToZero:=grid.goL backRoute (by decide) room
  let tPrefix:=1+((D 10-D 0+14)+(1+(1+(1+(1+(D 10-D 0+10))))))
  have prefixPath : Path P tPrefix (node (returnState (SerializedBody.sourceMode source c) b) (D 0) T) (node cleanup (D 0) T):=
    initial.append (scan.append (one.append (two.append (three.append (finish.append returnToZero)))))
  obtain ⟨cleared,clearedGrid,unchanged⟩:=clear_plan grid room plan
  let U:=scrub D successEdits T
  have below (i : Nat) (hi : i < F+1) : U i=T i:=unchanged i (by omega)
  have d0blank : U (F+1)=none := by rw [←anchor];exact grid_blank clearedGrid 0 (by decide)
  have sourceFence : F+1 ≤ P := by rw [←anchor];exact top 0 (by decide)
  have priceClear : clearCost D successEdits ≤ 5*(2*P+24) := by
    have p:=clearCost_le (grid_mono grid) room successEdits_bound
    exact p
  have prefixPrice : tPrefix ≤ 2*P+29 := by have :=top 10 (by decide);dsimp only [tPrefix];omega
  by_cases physical : c < S
  · have restoreCode : RestoreRows (Pnp4.Frontier.ContractExpansion.padRead source c) restore (SerializedBody.done b) := by
      simp only [SerializedBody.sourceMode,physical,↓reduceDIte] at restoreRows
      cases bit : source ⟨c,physical⟩ <;> simpa [bit,Pnp4.Frontier.ContractExpansion.padRead,physical] using restoreRows
    have returned:=restore_run sl lh physical positive arena sourceFence
      (by rw [below S (by omega)];exact eof) (by rw [below L (by omega)];exact left)
      (by rw [below H (by omega)];exact right) d0blank
      (by rw [below F (by omega)];exact fence) (by rw [below c (by omega)];exact hole physical)
      (by intro i lo hi;rw [below i (by omega)];exact reg i lo hi)
      (by intro i lo hi;rw [below i (by omega)];exact ass i lo hi)
      (by intro i lo hi;rw [below i (by omega)];exact marks i lo hi)
      (by intro i lo hi;rw [below i (by omega)];exact gap i lo hi)
      (by intro i lo hi;rw [below i (by omega)];exact src i lo hi) restoreCode
    rw [←anchor] at returned
    have total:=prefixPath.append (cleared.append returned)
    refine ⟨tPrefix+(clearCost D successEdits+((F+2-H)+(H-S+2)+(2*(S-c)+1)+(H-S+2))),?_,?_⟩
    · have fh : F+2-H ≤ P+2 := by omega
      have priceRestore : (F+2-H)+(H-S+2)+(2*(S-c)+1)+(H-S+2) ≤ 5*P+7 := by omega
      omega
    · simpa only [if_pos physical,U] using total
  · have restoreCode : ToHRows restore (SerializedBody.done b) := by
      simpa only [SerializedBody.sourceMode,physical,↓reduceDIte] using restoreRows
    have returned:=to_H positive arena sourceFence d0blank
      (by rw [below F (by omega)];exact fence) (by rw [below H (by omega)];exact right)
      (by intro i lo hi;rw [below i (by omega)];exact marks i lo hi)
      (by intro i lo hi;rw [below i (by omega)];exact gap i lo hi) restoreCode
    rw [←anchor] at returned
    have total:=prefixPath.append (cleared.append returned)
    refine ⟨tPrefix+(clearCost D successEdits+(F+2-H)),?_,?_⟩
    · have priceRestore : F+2-H ≤ P+2 := by omega
      omega
    · simpa only [if_neg physical,U] using total
end FullBodyClosure
