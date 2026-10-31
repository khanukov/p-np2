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
-- All navigation below is actual tape traversal; p is a proof coordinate of a real hole.
private def BetaSeekRows (start out : Fin 7500) : Prop :=
  ∃ enter scan : Fin 7500, ToHRows start enter ∧ 4 ≤ enter.val ∧ 4 ≤ scan.val ∧
    SerializedBody.machine.step enter none=(scan,none,.left) ∧
    (∀ b,SerializedBody.machine.step scan (some b)=(scan,some b,.left)) ∧
    SerializedBody.machine.step scan none=(out,none,.stay)
private def BetaReturnRows (start out : Fin 7500) : Prop :=
  ∃ next : Fin 7500,4 ≤ start.val ∧
    (∀ b,SerializedBody.machine.step start (some b)=(start,some b,.right)) ∧
    SerializedBody.machine.step start none=(next,none,.stay) ∧ FromHRows next out
private theorem beta_seek {T H Q F P p start out} (positive : 0 < Q) (arena : H+Q < F)
    (room : F+1 ≤ P) (d0 : T (F+1)=none) (fence : T F=some false) (header : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (inside : p < H) (hole : T p=none) (ass : ∀ i,p < i → i < H → ∃ b,T i=some b)
    (code : BetaSeekRows start out) :
    Path P (F+3-p) (node start (F+1) T) (node out p T) := by
  rcases code with ⟨enter,scan,toH,se,ss,re,rs,rn⟩
  have routed:=to_H positive arena room d0 fence header marks gap toH
  have head:=keep enter scan H (H-1) T .left (P:=P) (by omega) (by omega) se
    (by rw [header];exact re) rfl
  have mid:=sweepL scan T p (H-1-p) (P:=P) (by omega) ss (by
    intro i lo hi;obtain ⟨b,hb⟩:=ass i lo (by omega);rw [hb];exact rs b)
  rw [show p+(H-1-p)=H-1 by omega] at mid
  have last:=keep scan out p p T .stay (P:=P) (by omega) (by omega) ss
    (by rw [hole];exact rn) rfl
  have total:=routed.append (head.append (mid.append last))
  have price : (F+2-H)+(1+(H-1-p+1))=F+3-p := by omega
  rw [price] at total
  exact total
private theorem beta_return {T H Q F P p start out} (positive : 0 < Q) (arena : H+Q < F)
    (room : F+1 ≤ P) (fence : T F=some false) (header : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (inside : p ≤ H) (ass : ∀ i,p ≤ i → i < H → ∃ b,T i=some b)
    (code : BetaReturnRows start out) :
    Path P (F+2-p) (node start p T) (node out (F+1) T) := by
  rcases code with ⟨next,safe,loop,stop,fromH⟩
  have scan:=sweepR start T p (H-p) (P:=P) (by omega) safe (by
    intro i lo hi;obtain ⟨b,hb⟩:=ass i lo (by omega);rw [hb];exact loop b)
  rw [show p+(H-p)=H by omega] at scan
  have last:=keep start next H H T .stay (P:=P) (by omega) (by omega) safe
    (by rw [header];exact stop) rfl
  have tail:=from_H positive arena room fence header marks gap fromH
  have total:=scan.append (last.append tail)
  have price : (H-p)+(1+(F+1-H))=F+2-p := by omega
  rw [price] at total
  exact total
private def BetaLiftRows (start : Fin 7500) (out : Bool → Fin 7500) : Prop :=
  ∃ toH enter take : Fin 7500,∃ ret : Bool → Fin 7500,
    4 ≤ start.val ∧ 4 ≤ enter.val ∧ 4 ≤ take.val ∧
    SerializedBody.machine.step start none=(toH,none,.stay) ∧ ToHRows toH enter ∧
    SerializedBody.machine.step enter none=(take,none,.left) ∧
    ∀ b,SerializedBody.machine.step take (some b)=(ret b,none,.right) ∧ BetaReturnRows (ret b) (out b)
private theorem beta_lift {T H Q F P start out} (positive : 0 < Q) (arena : H+Q < F)
    (room : F+1 ≤ P) (d0 : T (F+1)=none) (fence : T F=some false) (header : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hasPrevious : 0 < H) (b : Bool) (cell : T (H-1)=some b) (code : BetaLiftRows start out) :
    Path P (2*(F+2-H)+3) (node start (F+1) T) (node (out b) (F+1) (put T (H-1) none)) := by
  rcases code with ⟨toH,enter,take,ret,ss,se,st,jump,toHRows,left,reads⟩
  have head:=keep start toH (F+1) (F+1) T .stay (P:=P) room room ss (by rw [d0];exact jump) rfl
  have routed:=to_H positive arena room d0 fence header marks gap toHRows
  have one:=keep enter take H (H-1) T .left (P:=P) (by omega) (by omega) se (by rw [header];exact left) rfl
  have lift:=hop take (ret b) (H-1) H T none .right (P:=P) (by omega) (by omega) st
    (by rw [cell];exact (reads b).1) (by change H-1+1=H;omega)
  let U:=put T (H-1) none
  have above (i : Nat) (hi : H ≤ i) : U i=T i := by
    change (if i=H-1 then none else T i)=T i
    exact if_neg (by omega)
  have back:=beta_return (T:=U) positive arena room
    (by rw [above F (by omega)];exact fence) (by rw [above H le_rfl];exact header)
    (by intro i lo hi;rw [above i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [above i (by omega)];exact gap i lo hi)
    (p:=H) (by omega) (by intro i lo hi;omega) (reads b).2
  have total:=head.append (routed.append (one.append (lift.append back)))
  have price : 1+((F+2-H)+(1+(1+(F+2-H))))=2*(F+2-H)+3 := by omega
  rw [price] at total
  exact total
private def BetaMoveRows (start : Fin 7500) (held : Bool) (out : Bool → Fin 7500) : Prop :=
  ∃ restore lift : Fin 7500,∃ ret : Bool → Fin 7500,
    BetaSeekRows start restore ∧ 4 ≤ restore.val ∧ 4 ≤ lift.val ∧
    SerializedBody.machine.step restore none=(lift,some held,.left) ∧
    ∀ next,SerializedBody.machine.step lift (some next)=(ret next,none,.right) ∧ BetaReturnRows (ret next) (out next)
private theorem beta_move {T H Q F P p start out} (positive : 0 < Q) (arena : H+Q < F)
    (room : F+1 ≤ P) (d0 : T (F+1)=none) (fence : T F=some false) (header : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (inside : p < H) (pos : 0 < p) (hole : T p=none)
    (ass : ∀ i,p < i → i < H → ∃ b,T i=some b)
    (held next : Bool) (cell : T (p-1)=some next) (code : BetaMoveRows start held out) :
    Path P (2*(F+3-p)+1) (node start (F+1) T)
      (node (out next) (F+1) (put (put T p (some held)) (p-1) none)) := by
  rcases code with ⟨restore,lift,ret,seek,sr,sl,write,reads⟩
  have seekPath:=beta_seek positive arena room d0 fence header marks gap inside hole ass seek
  let U:=put T p (some held)
  let V:=put U (p-1) none
  have one:=hop restore lift p (p-1) T (some held) .left (P:=P) (by omega) (by omega) sr
    (by rw [hole];exact write) rfl
  have atNext : U (p-1)=some next := by
    change (if p-1=p then some held else T (p-1))=some next
    rw [if_neg (by omega : p-1≠p)];exact cell
  have two:=hop lift (ret next) (p-1) p U none .right (P:=P) (by omega) (by omega) sl
    (by rw [atNext];exact (reads next).1) (by change p-1+1=p;omega)
  have above (i : Nat) (hi : H ≤ i) : V i=T i := by
    change (if i=p-1 then none else if i=p then some held else T i)=T i
    rw [if_neg (by omega : i≠p-1),if_neg (by omega : i≠p)]
  have rest:=beta_return (T:=V) positive arena room
    (by rw [above F (by omega)];exact fence) (by rw [above H le_rfl];exact header)
    (by intro i lo hi;rw [above i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [above i (by omega)];exact gap i lo hi)
    (p:=p) (by omega) (by
      intro i lo hi
      change ∃ b,(if i=p-1 then none else if i=p then some held else T i)=some b
      rw [if_neg (by omega : i≠p-1)]
      by_cases eq : i=p
      · exact ⟨held,by rw [if_pos eq]⟩
      · rw [if_neg eq];exact ass i (by omega) hi) (reads next).2
  have total:=seekPath.append (one.append (two.append rest))
  have price : (F+3-p)+(1+(1+(F+2-p)))=2*(F+3-p)+1 := by omega
  rw [price] at total
  exact total
private def BetaDoneRows (start out : Fin 7500) (held : Bool) : Prop :=
  ∃ restore ret : Fin 7500,BetaSeekRows start restore ∧ 4 ≤ restore.val ∧
    SerializedBody.machine.step restore none=(ret,some held,.right) ∧ BetaReturnRows ret out
private theorem beta_done {T H Q F P p start out} (positive : 0 < Q) (arena : H+Q < F)
    (room : F+1 ≤ P) (d0 : T (F+1)=none) (fence : T F=some false) (header : T H=none)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (inside : p < H) (hole : T p=none)
    (ass : ∀ i,p < i → i < H → ∃ b,T i=some b)
    (held : Bool) (code : BetaDoneRows start out held) :
    Path P ((F+3-p)+1+(F+2-(p+1))) (node start (F+1) T)
      (node out (F+1) (put T p (some held))) := by
  rcases code with ⟨restore,ret,seek,safe,write,returns⟩
  have seekPath:=beta_seek positive arena room d0 fence header marks gap inside hole ass seek
  let U:=put T p (some held)
  have one:=hop restore ret p (p+1) T (some held) .right (P:=P) (by omega) (by omega) safe
    (by rw [hole];exact write) rfl
  have above (i : Nat) (hi : p < i) : U i=T i := by
    change (if i=p then some held else T i)=T i
    exact if_neg (by omega)
  have rest:=beta_return (T:=U) positive arena room
    (by rw [above F (by omega)];exact fence) (by rw [above H inside];exact header)
    (by intro i lo hi;rw [above i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [above i (by omega)];exact gap i lo hi)
    (p:=p+1) (by omega) (by intro i lo hi;rw [above i (by omega)];exact ass i (by omega) hi) returns
  have total:=seekPath.append (one.append rest)
  have price : (F+3-p)+(1+(F+2-(p+1)))=(F+3-p)+1+(F+2-(p+1)) := by omega
  rw [price] at total
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

private abbrev st : Nat → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Support "FullBodyClosure" "st"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Return "FullBodyClosure" "returnState"
private def lookupState (m : Fin 3) : Fin 7500 := st (#[2989,5376,7443][m.val]!)
private def lookupLoopState (m : Fin 3) (b : Bool) : Fin 7500 :=
  st (#[3017,5404,7471,3048,5432,7499][3*(if b then 1 else 0)+m.val]!)
private def LookupRows (m : Fin 3) : Prop :=
  ∃ dec zeroBranch positiveBranch : Bool → Fin 7500, ∀ b,
    4 ≤ (lookupLoopState m b).val ∧
    SerializedBody.machine.step (lookupLoopState m b) none=(dec b,none,.stay) ∧
    DecRows 1 (dec b) (zeroBranch b) (positiveBranch b) ∧
    BetaDoneRows (zeroBranch b) (returnState m b) b ∧
    BetaMoveRows (positiveBranch b) b (lookupLoopState m)
private def betaView (T : Nat → Option Bool) (D : Nat → Nat) (H v j : Nat) : Nat → Option Bool :=
  put (counter T D 1 v) (H-1-j) none
private theorem betaView_high {T D H v j i} (_before : H ≤ D 0) (_grid : Grid D T)
    (past : H ≤ i) (hn : j < H) : betaView T D H v j i=counter T D 1 v i := by
  have : H-1-j < H := by omega
  change (if i=H-1-j then none else counter T D 1 v i)=_
  exact if_neg (by omega)
private theorem counter_low {T D v i} (grid : Grid D T) (low : i ≤ D 0) :
    counter T D 1 v i=T i := by
  have :=grid_mono grid 0 1 (by decide) (by decide)
  exact if_neg (by omega)
private theorem betaView_low {T D H v j i} (grid : Grid D T) (before : H ≤ D 0)
    (low : i < H) : betaView T D H v j i=(if i=H-1-j then none else T i) := by
  change (if i=H-1-j then none else counter T D 1 v i)=_
  rw [counter_low grid (by omega)]
private theorem betaView_grid {T D H v j} (grid : Grid D T) (before : H ≤ D 0)
    (hn : j < H) : Grid D (betaView T D H v j) := by
  have cg:=counter_grid grid 1 v (by decide)
  apply grid_make (grid_rise grid) (grid_mono grid)
  · intro k hk
    rw [betaView_high before grid (le_trans before (grid_mono grid 0 k (by omega) hk)) hn]
    exact grid_blank cg k hk
  · intro k i hk lo hi
    rw [betaView_high before grid (by have :=grid_mono grid 0 k (by omega) (by omega);omega) hn]
    exact grid_cells cg k i hk lo hi
private theorem betaView_down {T D H v j n} (grid : Grid D T) (before : H ≤ D 0)
    (len : D 2=D 1+n+1) (pos : 0 < v) (small : v ≤ n) (hn : j < H) :
    put (betaView T D H v j) (D 1+v) (some false)=betaView T D H (v-1) j := by
  have different : D 1+v≠H-1-j := by
    have :=grid_mono grid 0 1 (by decide) (by decide);omega
  have commute : put (put (counter T D 1 v) (H-1-j) none) (D 1+v) (some false)=
      put (put (counter T D 1 v) (D 1+v) (some false)) (H-1-j) none := by
    funext i
    change (if i=D 1+v then some false else if i=H-1-j then none else _)=
      (if i=H-1-j then none else if i=D 1+v then some false else _)
    by_cases a : i=D 1+v <;> by_cases b : i=H-1-j <;> simp_all
  rw [betaView,commute,counter_down T D 1 v n len pos small]
  rfl
private theorem betaView_move {T D H v j n} (grid : Grid D T) (before : H ≤ D 0)
    (beta : Fin n → Bool) (_hn : n < H) (small : j+1 < n)
    (cells : ∀ k : Fin n,T (H-1-k.val)=some (beta k)) :
    put (put (betaView T D H v j) (H-1-j) (some (beta ⟨j,by omega⟩)))
      (H-1-j-1) none=betaView T D H v (j+1) := by
  funext i
  change (if i=H-1-j-1 then none else if i=H-1-j then some (beta ⟨j,by omega⟩)
    else betaView T D H v j i)=betaView T D H v (j+1) i
  have sub : H-1-j-1=H-1-(j+1) := by omega
  rw [sub]
  by_cases next : i=H-1-(j+1)
  · rw [if_pos next]
    change none=(if i=H-1-(j+1) then none else counter T D 1 v i)
    rw [if_pos next]
  · rw [if_neg next]
    change _=(if i=H-1-(j+1) then none else counter T D 1 v i)
    rw [if_neg next]
    by_cases here : i=H-1-j
    · rw [if_pos here,here,counter_low grid (by omega)]
      exact (cells ⟨j,by omega⟩).symm
    · rw [if_neg here]
      change (if i=H-1-j then none else counter T D 1 v i)=counter T D 1 v i
      rw [if_neg here]
private theorem betaView_done {T D H j n} (grid : Grid D T) (before : H ≤ D 0)
    (beta : Fin n → Bool) (_hn : n < H) (small : j < n)
    (cells : ∀ k : Fin n,T (H-1-k.val)=some (beta k)) :
    put (betaView T D H 0 j) (H-1-j) (some (beta ⟨j,small⟩))=counter T D 1 0 := by
  funext i
  change (if i=H-1-j then some (beta ⟨j,small⟩) else if i=H-1-j then none else _)=_
  by_cases here : i=H-1-j
  · rw [if_pos here,here,counter_low grid (by omega)]
    exact (cells ⟨j,small⟩).symm
  · simp only [if_neg here]
private theorem beta_loop_budget (P v a b c : Nat) (_pv : v ≤ P) (ha : a ≤ 4*P+16)
    (hb : b ≤ 2*P+7) (hc : c ≤ 128*v*(P+1)) :
    1+a+b+c ≤ 128*(v+1)*(P+1) := by nlinarith
private theorem beta_loop {T D H Q F P n} (m : Fin 3) (grid : Grid D T)
    (before : H ≤ D 0) (d0 : D 0=F+1) (fit : D 12 ≤ P) (len : D 2=D 1+n+1)
    (positive : 0 < Q) (arena : H+Q < F) (hn : n < H)
    (header : T H=none) (fence : T F=some false)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (beta : Fin n → Bool) (cells : ∀ k : Fin n,T (H-1-k.val)=some (beta k))
    (code : LookupRows m) :
    ∀ v j,(bound : j+v < n) → ∃ t,t ≤ 128*(v+1)*(P+1) ∧
      Path P t (node (lookupLoopState m (beta ⟨j,by omega⟩)) (D 0) (betaView T D H v j))
        (node (returnState m (beta ⟨j+v,by omega⟩)) (D 0) (counter T D 1 0)) := by
  rcases code with ⟨dec,zeroBranch,positiveBranch,rows⟩
  have np : n ≤ P := by
    have :=grid_mono grid 2 12 (by decide) (by decide);omega
  have rootFit : D 0 ≤ P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) fit
  have bankFit : D 1 ≤ P:=le_trans (grid_mono grid 1 12 (by decide) (by decide)) fit
  intro v
  induction v with
  | zero =>
    intro j bound
    let b:=beta ⟨j,by omega⟩
    have g:=betaView_grid (v:=0) grid before (by omega : j < H)
    have jump:=keep (lookupLoopState m b) (dec b) (D 0) (D 0) (betaView T D H 0 j) .stay (P:=P)
      rootFit rootFit (rows b).1 (by rw [grid_blank g 0 (by decide)];exact (rows b).2.1) rfl
    have unary : Unary D (betaView T D H 0 j) 1 0 := by
      intro i lo hi
      rw [betaView_high before grid (by have :=grid_mono grid 0 1 (by decide) (by decide);omega) (by omega)]
      exact counter_unary T D 1 0 i lo hi
    have down:=dec_zero g (by decide) fit len unary (rows b).2.2.1
    -- Header/table geometry is outside bank1 and outside the beta hole.
    have atCell (i : Nat) (lo : H ≤ i) (up : i < D 0) : betaView T D H 0 j i=T i := by
      rw [betaView_high before grid lo (by omega),counter_low grid (by omega)]
    have tail:=beta_done (P:=P) (T:=betaView T D H 0 j) positive arena (by omega)
      (grid_blank g 0 (by decide) |> fun h=>by simpa only [d0] using h)
      (by rw [atCell F (by omega) (by omega)];exact fence)
      (by rw [atCell H le_rfl (by omega)];exact header)
      (by intro i lo hi;rw [atCell i (by omega) (by omega)];exact marks i lo hi)
      (by intro i lo hi;rw [atCell i (by omega) (by omega)];exact gap i lo hi)
      (p:=H-1-j) (by omega) (by change (if H-1-j=H-1-j then none else _)=none;exact if_pos rfl)
      (by
        intro i lo hi
        let k:=H-1-i
        have hk : k < n := by dsimp only [k];omega
        have eq : H-1-k=i := by dsimp only [k];omega
        refine ⟨beta ⟨k,hk⟩,?_⟩
        rw [betaView_low grid before hi,if_neg (by omega),←eq]
        exact cells ⟨k,hk⟩) b (rows b).2.2.2.1
    rw [betaView_done grid before beta hn (by omega) cells,←d0] at tail
    have path:=jump.append (down.append tail)
    refine ⟨_,?_,path⟩
    have h1:=grid_mono grid 1 12 (by decide) (by decide)
    have order:=grid_mono grid 0 1 (by decide) (by decide)
    omega
  | succ v ih =>
    intro j bound
    let b:=beta ⟨j,by omega⟩
    have g:=betaView_grid (v:=v+1) grid before (by omega : j < H)
    have jump:=keep (lookupLoopState m b) (dec b) (D 0) (D 0) (betaView T D H (v+1) j) .stay (P:=P)
      rootFit rootFit (rows b).1 (by rw [grid_blank g 0 (by decide)];exact (rows b).2.1) rfl
    have unary : Unary D (betaView T D H (v+1) j) 1 (v+1) := by
      intro i lo hi
      rw [betaView_high before grid (by have :=grid_mono grid 0 1 (by decide) (by decide);omega) (by omega)]
      exact counter_unary T D 1 (v+1) i lo hi
    have down:=dec_positive g (by decide) fit len unary (by omega) (by omega) (rows b).2.2.1
    rw [betaView_down grid before len (by omega) (by omega) (by omega)] at down
    simp only [Nat.add_sub_cancel] at down
    have atCell (i : Nat) (lo : H ≤ i) (up : i < D 0) : betaView T D H v j i=T i := by
      rw [betaView_high before grid lo (by omega),counter_low grid (by omega)]
    have move:=beta_move (P:=P) (T:=betaView T D H v j) positive arena (by omega)
      (by simpa only [d0] using grid_blank (betaView_grid (v:=v) grid before (by omega : j < H)) 0 (by decide))
      (by rw [atCell F (by omega) (by omega)];exact fence)
      (by rw [atCell H le_rfl (by omega)];exact header)
      (by intro i lo hi;rw [atCell i (by omega) (by omega)];exact marks i lo hi)
      (by intro i lo hi;rw [atCell i (by omega) (by omega)];exact gap i lo hi)
      (p:=H-1-j) (by omega) (by omega) (by change (if H-1-j=H-1-j then none else _)=none;exact if_pos rfl)
      (by
        intro i lo hi
        let k:=H-1-i
        have hk : k < n := by dsimp only [k];omega
        have eq : H-1-k=i := by dsimp only [k];omega
        refine ⟨beta ⟨k,hk⟩,?_⟩
        rw [betaView_low grid before hi,if_neg (by omega),←eq]
        exact cells ⟨k,hk⟩) b (beta ⟨j+1,by omega⟩)
      (by
        rw [betaView_low grid before (by omega),if_neg (by omega)]
        rw [show H-1-j-1=H-1-(j+1) by omega]
        exact cells ⟨j+1,by omega⟩) (rows b).2.2.2.2
    rw [betaView_move grid before beta hn (by omega) cells,←d0] at move
    obtain ⟨t,price,tail⟩:=ih (j+1) (by omega)
    have same : (⟨j+1+v,by omega⟩ : Fin n)=⟨j+(v+1),bound⟩ := by
      apply Fin.ext
      change j+1+v=j+(v+1)
      omega
    rw [same] at tail
    have path:=jump.append (down.append (move.append tail))
    refine ⟨_,?_,path⟩
    have order:=grid_mono grid 0 1 (by decide) (by decide)
    have decBound : 2*(D 1-D 0+1)+2*(v+1)+4 ≤ 4*P+16 := by omega
    have moveBound : 2*(F+3-(H-1-j))+1 ≤ 2*P+7 := by omega
    have q:=beta_loop_budget P (v+1) (2*(D 1-D 0+1)+2*(v+1)+4)
      (2*(F+3-(H-1-j))+1) t (by omega) decBound moveBound price
    simpa only [Nat.add_assoc] using q
private theorem beta_lookup {T D H Q F P n} (m : Fin 3) (grid : Grid D T)
    (before : H ≤ D 0) (d0 : D 0=F+1) (fit : D 12 ≤ P) (len : D 2=D 1+n+1)
    (positive : 0 < Q) (arena : H+Q < F) (hn : n < H)
    (header : T H=none) (fence : T F=some false)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap : ∀ i,H+Q < i → i < F → T i=none)
    (beta : Fin n → Bool) (cells : ∀ k : Fin n,T (H-1-k.val)=some (beta k))
    (index : Fin n) (liftCode : BetaLiftRows (lookupState m) (lookupLoopState m))
    (loopCode : LookupRows m) :
    ∃ t,t ≤ 256*(n+1)*(P+1) ∧
      Path P t (node (lookupState m) (D 0) (counter T D 1 index.val))
        (node (returnState m (beta index)) (D 0) (counter T D 1 0)) := by
  have hindex:=index.isLt
  have cg:=counter_grid grid 1 index.val (by decide)
  have rootFit : D 0 ≤ P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) fit
  have low (i : Nat) (hi : i≤D 0) : counter T D 1 index.val i=T i:=counter_low grid hi
  have entry:=beta_lift (P:=P) (T:=counter T D 1 index.val) positive arena (by omega)
    (by simpa only [d0] using grid_blank cg 0 (by decide))
    (by rw [low F (by omega)];exact fence)
    (by rw [low H before];exact header)
    (by intro i lo hi;rw [low i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact gap i lo hi)
    (by omega) (beta ⟨0,by omega⟩)
    (by rw [low (H-1) (by omega)];exact cells ⟨0,by omega⟩) liftCode
  change Path P (2*(F+2-H)+3) (node (lookupState m) (F+1) (counter T D 1 index.val))
    (node (lookupLoopState m (beta ⟨0,by omega⟩)) (F+1) (betaView T D H index.val 0)) at entry
  rw [←d0] at entry
  obtain ⟨t,price,tail⟩:=beta_loop m grid before d0 fit len positive arena hn header fence marks gap beta cells loopCode index.val 0 (by omega)
  simp only [Nat.zero_add] at tail
  have path:=entry.append tail
  refine ⟨_,?_,path⟩
  have liftPrice : 2*(F+2-H)+3 ≤ 4*(P+1) := by omega
  have scaled:=Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_left 128 (show index.val+1≤n from by omega))
  have smaller:=le_trans price scaled
  nlinarith
end FullBodyClosure
