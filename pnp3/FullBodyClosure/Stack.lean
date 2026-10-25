import FullBodyClosure.Return
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
private def PushRows (start out : Fin 7500) (b0 b1 b2 : Bool) : Prop :=
  ∃ enter : Fin 7500, ∃ q : Fin 7 → Fin 7500, ∃ found write1 write0 back ret : Fin 7500,
    4 ≤ enter.val ∧ 4 ≤ found.val ∧ 4 ≤ write1.val ∧ 4 ≤ write0.val ∧ 4 ≤ back.val ∧
    RouteR 0 10 start enter ∧ StackRows q found ∧
    SerializedBody.machine.step enter none=(q 0,none,.right) ∧
    SerializedBody.machine.step found (some true)=(write1,some b2,.left) ∧
    SerializedBody.machine.step write1 (some true)=(write0,some b1,.left) ∧
    SerializedBody.machine.step write0 (some true)=(back,some b0,.stay) ∧
    (∀ b,SerializedBody.machine.step back (some b)=(back,some b,.left)) ∧
    SerializedBody.machine.step back none=(ret,none,.stay) ∧ RouteL 10 0 ret out
private theorem push_path {D T P start out d b0 b1 b2} (grid : Grid D T)
    (room : D 12 ≤ P) (fieldRoom : D 10+3*d+4 ≤ D 11)
    (busy : ∀ j,j < d → ∃ a b c : Bool,(a && b && c)=false ∧
      T (D 10+1+3*j)=some a ∧ T (D 10+1+3*j+1)=some b ∧ T (D 10+1+3*j+2)=some c)
    (free0 : T (D 10+3*d+1)=some true) (free1 : T (D 10+3*d+2)=some true)
    (free2 : T (D 10+3*d+3)=some true) (code : PushRows start out b0 b1 b2) :
    let U:=put (put (put T (D 10+3*d+3) (some b2)) (D 10+3*d+2) (some b1)) (D 10+3*d+1) (some b0)
    Path P (2*(D 10-D 0)+6*d+29) (node start (D 0) T) (node out (D 0) U) := by
  dsimp only
  rcases code with ⟨enter,q,found,write1,write0,back,ret,se,sf,s1,s0,sb,route,rows,re,r2,r1,r0,rl,rn,returnRoute⟩
  have lastFit : D 11 ≤ P:=le_trans (grid_mono grid 11 12 (by decide) (by decide)) room
  let a:=D 10+3*d+1
  let T1:=put T (a+2) (some b2)
  let T2:=put T1 (a+1) (some b1)
  let T3:=put T2 a (some b0)
  have c0 : T a=some true:=free0
  have c1 : T (a+1)=some true:=free1
  have c2 : T (a+2)=some true:=free2
  have c1' : T1 (a+1)=some true := by
    change (if a+1=a+2 then some b2 else T (a+1))=some true
    rw [if_neg (by omega : a+1≠a+2)];exact c1
  have c0' : T2 a=some true := by
    change (if a=a+1 then some b1 else if a=a+2 then some b2 else T a)=some true
    rw [if_neg (by omega : a≠a+1),if_neg (by omega : a≠a+2)];exact c0
  have g1 : Grid D T1:=grid.change_some (a+2) true b2 c2
  have g2 : Grid D T2:=g1.change_some (a+1) true b1 c1'
  have g3 : Grid D T3:=g2.change_some a true b0 c0'
  have scan:=stack_scan (P:=P) grid route se re rows room fieldRoom busy
    (by convert free0 using 2;omega)
    (by convert free1 using 2;omega)
    (by convert free2 using 2;omega)
  change Path P (D 10-D 0+3*d+14) (node start (D 0) T) (node found (a+2) T) at scan
  have write2:=hop found write1 (a+2) (a+1) T (some b2) .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) sf
    (by rw [c2];exact r2) (by change a+2-1=a+1;omega)
  have write1Path:=hop write1 write0 (a+1) a T1 (some b1) .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) s1
    (by rw [c1'];exact r1) (by change a+1-1=a;omega)
  have write0Path:=hop write0 back a a T2 (some b0) .stay (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) s0
    (by rw [c0'];exact r0) rfl
  have retreat:=sweepL back T3 (D 10) (3*d+1) (P:=P) (by omega) sb (by
    intro i lo hi;obtain ⟨b,hb⟩:=grid_cells g3 10 i (by decide) lo (by change i < D 11;omega);rw [hb];exact rl b)
  have exit:=keep back ret (D 10) (D 10) T3 .stay (P:=P) (by omega) (by omega) sb
    (by rw [grid_blank g3 10 (by decide)];exact rn) rfl
  have tail:=g3.goL returnRoute (by decide) room
  have total:=scan.append (write2.append (write1Path.append (write0Path.append (retreat.append (exit.append tail)))))
  have time : (D 10-D 0+3*d+14)+(1+(1+(1+(3*d+1+(1+(D 10-D 0+(10-0)))))))=
      2*(D 10-D 0)+6*d+29 := by omega
  rw [time] at total
  exact total
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
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Return "FullBodyClosure" "returnState"
private def bit0 (c : Fin 7) : Bool := decide (4 ≤ c.val)
private def bit1 (c : Fin 7) : Bool := decide (2 ≤ c.val%4)
private def bit2 (c : Fin 7) : Bool := decide (c.val%2=1)
private theorem record_not_free (c : Fin 7) : (bit0 c && bit1 c && bit2 c)=false := by fin_cases c <;> decide
private def PopRows (m : Fin 3) (b : Bool) (out : Fin 7 → Fin 7500) : Prop :=
  ∃ scanStart enter : Fin 7500, ∃ q : Fin 7 → Fin 7500, ∃ found r1 r2 last : Fin 7500,
    ∃ second first back ret : Fin 7 → Fin 7500,
    4 ≤ (returnState m b).val ∧ 4 ≤ enter.val ∧ 4 ≤ found.val ∧ 4 ≤ r1.val ∧ 4 ≤ r2.val ∧ 4 ≤ last.val ∧
    (∀ c,4 ≤ (second c).val ∧ 4 ≤ (first c).val ∧ 4 ≤ (back c).val ∧ 4 ≤ (out c).val) ∧
    SerializedBody.machine.step (returnState m b) none=(scanStart,none,.stay) ∧
    RouteR 0 10 scanStart enter ∧ StackRows q found ∧
    SerializedBody.machine.step enter none=(q 0,none,.right) ∧
    (∀ x,SerializedBody.machine.step found x=(r1,x,.left)) ∧
    (∀ x,SerializedBody.machine.step r1 x=(r2,x,.left)) ∧
    (∀ x,SerializedBody.machine.step r2 x=(last,x,.left)) ∧
    ∀ c, SerializedBody.machine.step last (some (bit2 c))=(second c,some true,.left) ∧
      SerializedBody.machine.step (second c) (some (bit1 c))=(first c,some true,.left) ∧
      SerializedBody.machine.step (first c) (some (bit0 c))=(back c,some true,.stay) ∧
      (∀ x,SerializedBody.machine.step (back c) (some x)=(back c,some x,.left)) ∧
      SerializedBody.machine.step (back c) none=(ret c,none,.stay) ∧ RouteL 10 0 (ret c) (out c)
private theorem pop_path {D T P d out} (m : Fin 3) (b : Bool) (c : Fin 7) (grid : Grid D T)
    (room : D 12 ≤ P) (fieldRoom : D 10+3*(d+1)+4 ≤ D 11)
    (busy : ∀ j,j < d → ∃ a b c : Bool,(a && b && c)=false ∧
      T (D 10+1+3*j)=some a ∧ T (D 10+1+3*j+1)=some b ∧ T (D 10+1+3*j+2)=some c)
    (old0 : T (D 10+3*d+1)=some (bit0 c)) (old1 : T (D 10+3*d+2)=some (bit1 c))
    (old2 : T (D 10+3*d+3)=some (bit2 c))
    (free0 : T (D 10+3*(d+1)+1)=some true) (free1 : T (D 10+3*(d+1)+2)=some true)
    (free2 : T (D 10+3*(d+1)+3)=some true) (code : PopRows m b out) :
    let U:=put (put (put T (D 10+3*d+3) (some true)) (D 10+3*d+2) (some true)) (D 10+3*d+1) (some true)
    Path P (2*(D 10-D 0)+6*d+36) (node (returnState m b) (D 0) T) (node (out c) (D 0) U) := by
  dsimp only
  rcases code with ⟨scanStart,enter,q,found,r1,r2,last,second,first,back,ret,
    safe,se,sf,sr1,sr2,sl,safeAll,jump,route,rows,entry,mv0,mv1,mv2,branches⟩
  have lastFit : D 11 ≤ P:=le_trans (grid_mono grid 11 12 (by decide) (by decide)) room
  have rootFit : D 0 ≤ P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
  let a:=D 10+3*d+1
  let T1:=put T (a+2) (some true)
  let T2:=put T1 (a+1) (some true)
  let T3:=put T2 a (some true)
  have c0 : T a=some (bit0 c):=old0
  have c1 : T (a+1)=some (bit1 c):=old1
  have c2 : T (a+2)=some (bit2 c):=old2
  have c1' : T1 (a+1)=some (bit1 c) := by
    change (if a+1=a+2 then some true else T (a+1))=some (bit1 c)
    rw [if_neg (by omega : a+1≠a+2)];exact c1
  have c0' : T2 a=some (bit0 c) := by
    change (if a=a+1 then some true else if a=a+2 then some true else T a)=some (bit0 c)
    rw [if_neg (by omega : a≠a+1),if_neg (by omega : a≠a+2)];exact c0
  have g1 : Grid D T1:=grid.change_some (a+2) (bit2 c) true c2
  have g2 : Grid D T2:=g1.change_some (a+1) (bit1 c) true c1'
  have g3 : Grid D T3:=g2.change_some a (bit0 c) true c0'
  have one:=keep (returnState m b) scanStart (D 0) (D 0) T .stay (P:=P) rootFit rootFit safe
    (by rw [grid_blank grid 0 (by decide)];exact jump) rfl
  have scan:=stack_scan (P:=P) (d:=d+1) grid route se entry rows room fieldRoom (by
      intro j hj
      by_cases early : j < d
      · exact busy j early
      · have eq : j=d := by omega
        subst j
        refine ⟨bit0 c,bit1 c,bit2 c,record_not_free c,?_,?_,?_⟩
        · convert old0 using 2;omega
        · convert old1 using 2;omega
        · convert old2 using 2;omega)
    (by convert free0 using 2;omega) (by convert free1 using 2;omega) (by convert free2 using 2;omega)
  change Path P (D 10-D 0+3*(d+1)+14) (node scanStart (D 0) T) (node found (a+5) T) at scan
  have rpath1:=keep found r1 (a+5) (a+4) T .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) sf (mv0 _) (by change a+5-1=a+4;omega)
  have rpath2:=keep r1 r2 (a+4) (a+3) T .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) sr1 (mv1 _) (by change a+4-1=a+3;omega)
  have rpath3:=keep r2 last (a+3) (a+2) T .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) sr2 (mv2 _) (by change a+3-1=a+2;omega)
  rcases branches c with ⟨rd2,rd1,rd0,rl,rn,returnRoute⟩
  have erase2:=hop last (second c) (a+2) (a+1) T (some true) .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) sl
    (by rw [c2];exact rd2) (by change a+2-1=a+1;omega)
  have erase1:=hop (second c) (first c) (a+1) a T1 (some true) .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) (safeAll c).1
    (by rw [c1'];exact rd1) (by change a+1-1=a;omega)
  have erase0:=hop (first c) (back c) a a T2 (some true) .stay (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) (safeAll c).2.1
    (by rw [c0'];exact rd0) rfl
  have retreat:=sweepL (back c) T3 (D 10) (3*d+1) (P:=P) (by omega) (safeAll c).2.2.1 (by
    intro i lo hi;obtain ⟨v,hv⟩:=grid_cells g3 10 i (by decide) lo (by change i < D 11;omega);rw [hv];exact rl v)
  have exit:=keep (back c) (ret c) (D 10) (D 10) T3 .stay (P:=P) (by omega) (by omega) (safeAll c).2.2.1
    (by rw [grid_blank g3 10 (by decide)];exact rn) rfl
  have tail:=g3.goL returnRoute (by decide) room
  have total:=one.append (scan.append (rpath1.append (rpath2.append (rpath3.append
    (erase2.append (erase1.append (erase0.append (retreat.append (exit.append tail)))))))))
  have time : 1+((D 10-D 0+3*(d+1)+14)+(1+(1+(1+(1+(1+(1+(3*d+1+(1+(D 10-D 0+(10-0)))))))))))=
      2*(D 10-D 0)+6*d+36 := by omega
  rw [time] at total
  exact total
end FullBodyClosure
