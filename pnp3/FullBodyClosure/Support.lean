import SerializedBodyCompletion.Kernel
import SerializedPositiveBody.Driver
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
-- All objects below are proof-side: each edge refines one literal frozen row.
private def StackRows (q : Fin 7 → Fin 7500) (found : Fin 7500) : Prop :=
  (∀ p, 4 ≤ (q p).val) ∧
  (∀ p : Fin 3, ∀ b : Bool,
    SerializedBody.machine.step (q ⟨p.val,by omega⟩) (some b) =
      (q ⟨2*p.val+1+(if b then 1 else 0),by have := p.isLt; split <;> omega⟩,some b,.right)) ∧
  (∀ p : Fin 4, ∀ b : Bool,
    SerializedBody.machine.step (q ⟨p.val+3,by omega⟩) (some b) =
      ((if p.val=3 ∧ b=true then found else q 0),some b,
        if p.val=3 ∧ b=true then .stay else .right))
private theorem stack_record {P : Nat} {q : Fin 7 → Fin 7500} {found : Fin 7500}
    (rows : StackRows q found) (T : Nat → Option Bool) (h : Nat)
    (room : h+3 ≤ P) (a b c : Bool)
    (cell0 : T h=some a) (cell1 : T (h+1)=some b) (cell2 : T (h+2)=some c) :
    Path P 3 (node (q 0) h T)
      (node (if a && b && c then found else q 0) (if a && b && c then h+2 else h+3) T) := by
  let p1 : Fin 7:=if a then 2 else 1
  let p2 : Fin 7:=if a then if b then 6 else 5 else if b then 4 else 3
  have r0 : SerializedBody.machine.step (q 0) (some a)=(q p1,some a,.right) := by
    cases a <;> exact rows.2.1 (0 : Fin 3) _
  have r1 : SerializedBody.machine.step (q p1) (some b)=(q p2,some b,.right) := by
    cases a <;> cases b <;> first
    | exact rows.2.1 (1 : Fin 3) _
    | exact rows.2.1 (2 : Fin 3) _
  have r2 : SerializedBody.machine.step (q p2) (some c)=
      ((if a && b && c then found else q 0),some c,if a && b && c then .stay else .right) := by
    cases a <;> cases b <;> cases c <;> first
    | exact rows.2.2 (0 : Fin 4) _
    | exact rows.2.2 (1 : Fin 4) _
    | exact rows.2.2 (2 : Fin 4) _
    | exact rows.2.2 (3 : Fin 4) _
  have one:=keep (q 0) (q p1) h (h+1) T .right (P:=P) (by omega) (by omega)
    (rows.1 0) (by rw [cell0];exact r0) rfl
  have two:=keep (q p1) (q p2) (h+1) (h+2) T .right (P:=P) (by omega) (by omega)
    (rows.1 p1) (by rw [cell1];exact r1) rfl
  have last:=keep (q p2) (if a && b && c then found else q 0) (h+2)
    (if a && b && c then h+2 else h+3) T (if a && b && c then .stay else .right)
    (P:=P) (by omega) (by split <;> omega) (rows.1 p2) (by rw [cell2];exact r2)
    (by split <;> rfl)
  exact one.append (two.append last)
private theorem stack_records {P : Nat} {q : Fin 7 → Fin 7500} {found : Fin 7500}
    (rows : StackRows q found) (T : Nat → Option Bool) (h d : Nat)
    (room : h+3*d+3 ≤ P)
    (busy : ∀ j,j < d → ∃ a b c : Bool,
      (a && b && c)=false ∧ T (h+3*j)=some a ∧ T (h+3*j+1)=some b ∧ T (h+3*j+2)=some c)
    (free0 : T (h+3*d)=some true) (free1 : T (h+3*d+1)=some true) (free2 : T (h+3*d+2)=some true) :
    Path P (3*d+3) (node (q 0) h T) (node found (h+3*d+2) T) := by
  induction d generalizing h with
  | zero =>
    simpa only [Nat.mul_zero,Nat.add_zero,Bool.true_and,↓reduceIte] using
      stack_record (P:=P) rows T h room true true true free0 free1 free2
  | succ d ih =>
    obtain ⟨a,b,c,notfree,at0,at1,at2⟩:=busy 0 (by omega)
    have first:=stack_record (P:=P) rows T h (by omega) a b c (by simpa using at0) (by simpa using at1) (by simpa using at2)
    rw [notfree] at first
    simp only [Bool.false_eq_true,↓reduceIte] at first
    have rest:=ih (h+3) (by omega) (by
      intro j hj
      obtain ⟨x,y,z,bits,x0,x1,x2⟩:=busy (j+1) (by omega)
      refine ⟨x,y,z,bits,?_,?_,?_⟩
      · convert x0 using 2; omega
      · convert x1 using 2; omega
      · convert x2 using 2; omega)
      (by convert free0 using 2; omega)
      (by convert free1 using 2; omega)
      (by convert free2 using 2; omega)
    have total:=first.append rest
    have cost : 3+(3*d+3)=3*(d+1)+3 := by omega
    have endpoint : h+3+3*d+2=h+3*(d+1)+2 := by omega
    rw [cost,endpoint] at total
    exact total
private theorem stack_scan {D T P start enter q found d} (grid : Grid D T)
    (route : RouteR 0 10 start enter) (safe : 4 ≤ enter.val)
    (entry : SerializedBody.machine.step enter none=(q 0,none,.right))
    (rows : StackRows q found) (room : D 12 ≤ P) (fieldRoom : D 10+3*d+4 ≤ D 11)
    (busy : ∀ j,j < d → ∃ a b c : Bool,
      (a && b && c)=false ∧ T (D 10+1+3*j)=some a ∧ T (D 10+1+3*j+1)=some b ∧ T (D 10+1+3*j+2)=some c)
    (free0 : T (D 10+1+3*d)=some true) (free1 : T (D 10+1+3*d+1)=some true)
    (free2 : T (D 10+1+3*d+2)=some true) :
    Path P (D 10-D 0+3*d+14) (node start (D 0) T) (node found (D 10+3*d+3) T) := by
  have lastFit : D 11 ≤ P:=le_trans (grid_mono grid 11 12 (by decide) (by decide)) room
  have out:=grid.goR route (by decide) room
  have head:=keep enter (q 0) (D 10) (D 10+1) T .right (P:=P) (by omega) (by omega) safe
    (by rw [grid_blank grid 10 (by decide)];exact entry) rfl
  have scan:=stack_records (P:=P) rows T (D 10+1) d (by omega) busy free0 free1 free2
  have total:=out.append (head.append scan)
  have cost : (D 10-D 0+(10-0))+(1+(3*d+3))=D 10-D 0+3*d+14 := by omega
  have endpoint : D 10+1+3*d+2=D 10+3*d+3 := by omega
  rw [cost,endpoint] at total
  exact total
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
private def st (v : Nat) : Fin 7500 := ⟨v%7500,Nat.mod_lt _ (by decide)⟩
section LiteralStackRows
set_option maxRecDepth 4000
private def stages789 (p : Fin 7) : Fin 7500 := st (#[782,783,784,785,786,787,788][p.val]!)
private theorem scanRows789 : StackRows stages789 (st 758) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry789 : SerializedBody.machine.step (st 789) none=(stages789 0,none,.right) := rfl
private def stages841 (p : Fin 7) : Fin 7500 := st (#[834,835,836,837,838,839,840][p.val]!)
private theorem scanRows841 : StackRows stages841 (st 810) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry841 : SerializedBody.machine.step (st 841) none=(stages841 0,none,.right) := rfl
private def stages893 (p : Fin 7) : Fin 7500 := st (#[886,887,888,889,890,891,892][p.val]!)
private theorem scanRows893 : StackRows stages893 (st 862) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry893 : SerializedBody.machine.step (st 893) none=(stages893 0,none,.right) := rfl
private def stages924 (p : Fin 7) : Fin 7500 := st (#[917,918,919,920,921,922,923][p.val]!)
private theorem scanRows924 : StackRows stages924 (st 914) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry924 : SerializedBody.machine.step (st 924) none=(stages924 0,none,.right) := rfl
private def stages955 (p : Fin 7) : Fin 7500 := st (#[948,949,950,951,952,953,954][p.val]!)
private theorem scanRows955 : StackRows stages955 (st 945) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry955 : SerializedBody.machine.step (st 955) none=(stages955 0,none,.right) := rfl
private def stages986 (p : Fin 7) : Fin 7500 := st (#[979,980,981,982,983,984,985][p.val]!)
private theorem scanRows986 : StackRows stages986 (st 976) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry986 : SerializedBody.machine.step (st 986) none=(stages986 0,none,.right) := rfl
private def stages1119 (p : Fin 7) : Fin 7500 := st (#[1112,1113,1114,1115,1116,1117,1118][p.val]!)
private theorem scanRows1119 : StackRows stages1119 (st 1109) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1119 : SerializedBody.machine.step (st 1119) none=(stages1119 0,none,.right) := rfl
private def stages1150 (p : Fin 7) : Fin 7500 := st (#[1143,1144,1145,1146,1147,1148,1149][p.val]!)
private theorem scanRows1150 : StackRows stages1150 (st 1140) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1150 : SerializedBody.machine.step (st 1150) none=(stages1150 0,none,.right) := rfl
private def stages1181 (p : Fin 7) : Fin 7500 := st (#[1174,1175,1176,1177,1178,1179,1180][p.val]!)
private theorem scanRows1181 : StackRows stages1181 (st 1171) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1181 : SerializedBody.machine.step (st 1181) none=(stages1181 0,none,.right) := rfl
private def stages1521 (p : Fin 7) : Fin 7500 := st (#[1514,1515,1516,1517,1518,1519,1520][p.val]!)
private theorem scanRows1521 : StackRows stages1521 (st 1511) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1521 : SerializedBody.machine.step (st 1521) none=(stages1521 0,none,.right) := rfl
private def stages1552 (p : Fin 7) : Fin 7500 := st (#[1545,1546,1547,1548,1549,1550,1551][p.val]!)
private theorem scanRows1552 : StackRows stages1552 (st 1542) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1552 : SerializedBody.machine.step (st 1552) none=(stages1552 0,none,.right) := rfl
private def stages1863 (p : Fin 7) : Fin 7500 := st (#[1856,1857,1858,1859,1860,1861,1862][p.val]!)
private theorem scanRows1863 : StackRows stages1863 (st 1508) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1863 : SerializedBody.machine.step (st 1863) none=(stages1863 0,none,.right) := rfl
private def stages1898 (p : Fin 7) : Fin 7500 := st (#[1891,1892,1893,1894,1895,1896,1897][p.val]!)
private theorem scanRows1898 : StackRows stages1898 (st 1888) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1898 : SerializedBody.machine.step (st 1898) none=(stages1898 0,none,.right) := rfl
private def stages1929 (p : Fin 7) : Fin 7500 := st (#[1922,1923,1924,1925,1926,1927,1928][p.val]!)
private theorem scanRows1929 : StackRows stages1929 (st 1919) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry1929 : SerializedBody.machine.step (st 1929) none=(stages1929 0,none,.right) := rfl
private def stages2197 (p : Fin 7) : Fin 7500 := st (#[2190,2191,2192,2193,2194,2195,2196][p.val]!)
private theorem scanRows2197 : StackRows stages2197 (st 1885) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry2197 : SerializedBody.machine.step (st 2197) none=(stages2197 0,none,.right) := rfl
private def stages4147 (p : Fin 7) : Fin 7500 := st (#[4140,4141,4142,4143,4144,4145,4146][p.val]!)
private theorem scanRows4147 : StackRows stages4147 (st 4137) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry4147 : SerializedBody.machine.step (st 4147) none=(stages4147 0,none,.right) := rfl
private def stages4178 (p : Fin 7) : Fin 7500 := st (#[4171,4172,4173,4174,4175,4176,4177][p.val]!)
private theorem scanRows4178 : StackRows stages4178 (st 4168) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry4178 : SerializedBody.machine.step (st 4178) none=(stages4178 0,none,.right) := rfl
private def stages4484 (p : Fin 7) : Fin 7500 := st (#[4477,4478,4479,4480,4481,4482,4483][p.val]!)
private theorem scanRows4484 : StackRows stages4484 (st 4134) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry4484 : SerializedBody.machine.step (st 4484) none=(stages4484 0,none,.right) := rfl
private def stages4519 (p : Fin 7) : Fin 7500 := st (#[4512,4513,4514,4515,4516,4517,4518][p.val]!)
private theorem scanRows4519 : StackRows stages4519 (st 4509) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry4519 : SerializedBody.machine.step (st 4519) none=(stages4519 0,none,.right) := rfl
private def stages4550 (p : Fin 7) : Fin 7500 := st (#[4543,4544,4545,4546,4547,4548,4549][p.val]!)
private theorem scanRows4550 : StackRows stages4550 (st 4540) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry4550 : SerializedBody.machine.step (st 4550) none=(stages4550 0,none,.right) := rfl
private def stages4813 (p : Fin 7) : Fin 7500 := st (#[4806,4807,4808,4809,4810,4811,4812][p.val]!)
private theorem scanRows4813 : StackRows stages4813 (st 4506) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry4813 : SerializedBody.machine.step (st 4813) none=(stages4813 0,none,.right) := rfl
private def stages6280 (p : Fin 7) : Fin 7500 := st (#[6273,6274,6275,6276,6277,6278,6279][p.val]!)
private theorem scanRows6280 : StackRows stages6280 (st 6270) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry6280 : SerializedBody.machine.step (st 6280) none=(stages6280 0,none,.right) := rfl
private def stages6311 (p : Fin 7) : Fin 7500 := st (#[6304,6305,6306,6307,6308,6309,6310][p.val]!)
private theorem scanRows6311 : StackRows stages6311 (st 6301) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry6311 : SerializedBody.machine.step (st 6311) none=(stages6311 0,none,.right) := rfl
private def stages6591 (p : Fin 7) : Fin 7500 := st (#[6584,6585,6586,6587,6588,6589,6590][p.val]!)
private theorem scanRows6591 : StackRows stages6591 (st 6267) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry6591 : SerializedBody.machine.step (st 6591) none=(stages6591 0,none,.right) := rfl
private def stages6626 (p : Fin 7) : Fin 7500 := st (#[6619,6620,6621,6622,6623,6624,6625][p.val]!)
private theorem scanRows6626 : StackRows stages6626 (st 6616) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry6626 : SerializedBody.machine.step (st 6626) none=(stages6626 0,none,.right) := rfl
private def stages6657 (p : Fin 7) : Fin 7500 := st (#[6650,6651,6652,6653,6654,6655,6656][p.val]!)
private theorem scanRows6657 : StackRows stages6657 (st 6647) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry6657 : SerializedBody.machine.step (st 6657) none=(stages6657 0,none,.right) := rfl
private def stages6914 (p : Fin 7) : Fin 7500 := st (#[6907,6908,6909,6910,6911,6912,6913][p.val]!)
private theorem scanRows6914 : StackRows stages6914 (st 6613) := by
  refine ⟨?_,?_,?_⟩
  · intro p;fin_cases p <;> decide
  · intro p b;fin_cases p <;> cases b <;> rfl
  · intro p b;fin_cases p <;> cases b <;> rfl
private theorem scanEntry6914 : SerializedBody.machine.step (st 6914) none=(stages6914 0,none,.right) := rfl
end LiteralStackRows
end FullBodyClosure
