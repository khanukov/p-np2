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

private theorem path_nil : ∀ {P : Nat} (c : Node),nodeHead c ≤ P → Path P 0 c c := by run_tac checkedKernel "Path.nil"
private def AppendRows (start out : Fin 7500) (b : Bool) : Prop :=
  ∃ enter scan skip digit back ret : Fin 7500,
    4 ≤ enter.val ∧ 4 ≤ scan.val ∧ 4 ≤ skip.val ∧ 4 ≤ digit.val ∧ 4 ≤ back.val ∧
    RouteR 0 9 start enter ∧ RouteL 9 0 ret out ∧
    SerializedBody.machine.step enter none=(scan,none,.right) ∧
    SerializedBody.machine.step scan (some true)=(skip,some true,.right) ∧
    (∀ x,SerializedBody.machine.step skip (some x)=(scan,some x,.right)) ∧
    SerializedBody.machine.step scan (some false)=(digit,some true,.right) ∧
    (∀ x,SerializedBody.machine.step digit (some x)=(back,some b,.stay)) ∧
    (∀ x,SerializedBody.machine.step back (some x)=(back,some x,.left)) ∧
    SerializedBody.machine.step back none=(ret,none,.stay)

private theorem append_pairs {P : Nat} {T : Nat → Option Bool} {scan skip : Fin 7500} {a : Nat}
    (ss : 4 ≤ scan.val) (sk : 4 ≤ skip.val)
    (rs : SerializedBody.machine.step scan (some true)=(skip,some true,.right))
    (rk : ∀ b,SerializedBody.machine.step skip (some b)=(scan,some b,.right)) :
    ∀ d,a+2*d ≤ P →
      (∀ j,j<d → T (a+2*j)=some true ∧ ∃ b,T (a+2*j+1)=some b) →
      Path P (2*d) (node scan a T) (node scan (a+2*d) T) := by
  intro d
  induction d with
  | zero => intro room _cells;simpa only [Nat.mul_zero,Nat.add_zero] using path_nil (node scan a T) room
  | succ d ih =>
    intro room cells
    have prev:=ih (by omega) (by intro j hj;exact cells j (by omega))
    obtain ⟨flag,b,digit⟩:=cells d (by omega)
    have one:=keep scan skip (a+2*d) (a+2*d+1) T .right (P:=P) (by omega) (by omega) ss
      (by rw [flag];exact rs) rfl
    have two:=keep skip scan (a+2*d+1) (a+2*d+2) T .right (P:=P) (by omega) (by omega) sk
      (by rw [digit];exact rk b) rfl
    have total:=prev.append (one.append two)
    convert total using 1
private theorem append_path {D T P d start out} (b : Bool) (grid : Grid D T) (room : D 12 ≤ P)
    (fit : D 9+2*d+3 ≤ D 10)
    (busy : ∀ j,j<d → T (D 9+1+2*j)=some true ∧ ∃ b,T (D 9+1+2*j+1)=some b)
    (free : T (D 9+2*d+1)=some false) (freeDigit : ∃ b,T (D 9+2*d+2)=some b)
    (code : AppendRows start out b) :
    Path P (2*(D 9-D 0)+4*d+24) (node start (D 0) T)
      (node out (D 0) (put (put T (D 9+2*d+1) (some true)) (D 9+2*d+2) (some b))) := by
  rcases code with ⟨enter,scan,skip,digit,back,ret,se,ss,sk,sd,sb,forward,reverse,entry,rs,rk,rt,rd,rl,rn⟩
  have upper : D 10 ≤ P:=le_trans (grid_mono grid 10 12 (by decide) (by decide)) room
  have lower : D 9 ≤ D 10:=grid_mono grid 9 10 (by decide) (by decide)
  let a:=D 9+2*d+1
  let U:=put T a (some true)
  let V:=put U (a+1) (some b)
  have routed:=grid.goR forward (by decide) room
  have one:=keep enter scan (D 9) (D 9+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [grid_blank grid 9 (by decide)];exact entry) rfl
  have pairs:=append_pairs (P:=P) ss sk rs rk d (a:=D 9+1) (by omega) busy
  rw [show D 9+1+2*d=a by dsimp only [a];omega] at pairs
  have flag : T a=some false:=free
  have two:=hop scan digit a (a+1) T (some true) .right (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) ss
    (by rw [flag];exact rt) rfl
  obtain ⟨old,atDigit⟩:=freeDigit
  have atDigit' : U (a+1)=some old := by
    change (if a+1=a then some true else T (a+1))=some old
    rw [if_neg (by omega : a+1≠a)];exact atDigit
  have three:=hop digit back (a+1) (a+1) U (some b) .stay (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) sd
    (by rw [atDigit'];exact rd old) rfl
  have g1 : Grid D U:=grid.change_some a false true flag
  have g2 : Grid D V:=g1.change_some (a+1) old b atDigit'
  have retreat:=sweepL back V (D 9) (2*d+2) (P:=P) (by omega) sb (by
    intro i lo hi;obtain ⟨x,hx⟩:=grid_cells g2 9 i (by decide) lo (by change i<D 10;omega)
    rw [hx];exact rl x)
  have exit:=keep back ret (D 9) (D 9) V .stay (P:=P) (by omega) (by omega) sb
    (by rw [grid_blank g2 9 (by decide)];exact rn) rfl
  have tail:=g2.goL reverse (by decide) room
  have total:=routed.append (one.append (pairs.append (two.append (three.append (retreat.append (exit.append tail))))))
  have time : (D 9-D 0+9)+(1+(2*d+(1+(1+((2*d+2)+(1+(D 9-D 0+9)))))))=
      2*(D 9-D 0)+4*d+24 := by omega
  rw [time] at total
  exact total

private def PopBufferRows (start lookup : Fin 7500) (out : Bool → Fin 7500) : Prop :=
  ∃ enter scan skip take : Fin 7500,∃ flag back ret : Bool → Fin 7500,∃ empty : Fin 7500,
    4 ≤ enter.val ∧ 4 ≤ scan.val ∧ 4 ≤ skip.val ∧ 4 ≤ take.val ∧
    (∀ b,4 ≤ (flag b).val ∧ 4 ≤ (back b).val) ∧
    RouteR 0 9 start enter ∧ RouteL 9 0 empty lookup ∧
    (∀ b,RouteL 9 0 (ret b) (out b)) ∧
    SerializedBody.machine.step enter none=(scan,none,.right) ∧
    SerializedBody.machine.step scan (some true)=(skip,some true,.right) ∧
    (∀ b,SerializedBody.machine.step skip (some b)=(scan,some b,.right)) ∧
    (∀ x,x≠some true → SerializedBody.machine.step scan x=(take,x,.left)) ∧
    SerializedBody.machine.step take none=(empty,none,.stay) ∧
    ∀ b,SerializedBody.machine.step take (some b)=(flag b,some false,.left) ∧
      SerializedBody.machine.step (flag b) (some true)=(back b,some false,.left) ∧
      (∀ x,SerializedBody.machine.step (back b) (some x)=(back b,some x,.left)) ∧
      SerializedBody.machine.step (back b) none=(ret b,none,.stay)
private theorem pop_buffer_path {D T P d start lookup out} (grid : Grid D T) (room : D 12 ≤ P)
    (fit : D 9+2*(d+1)+1 ≤ D 10)
    (busy : ∀ j,j<d+1 → T (D 9+1+2*j)=some true ∧ ∃ b,T (D 9+1+2*j+1)=some b)
    (stop : T (D 9+1+2*(d+1))≠some true) (b : Bool)
    (last : T (D 9+2*d+2)=some b) (code : PopBufferRows start lookup out) :
    Path P (2*(D 9-D 0)+4*d+25) (node start (D 0) T)
      (node (out b) (D 0) (put (put T (D 9+2*d+2) (some false)) (D 9+2*d+1) (some false))) := by
  rcases code with ⟨enter,scan,skip,take,flag,back,ret,empty,se,ss,sk,st,safe,forward,emptyRoute,reverse,
    entry,rs,rk,rn,emptyRow,reads⟩
  have upper : D 10 ≤ P:=le_trans (grid_mono grid 10 12 (by decide) (by decide)) room
  let a:=D 9+2*d+1
  let U:=put T (a+1) (some false)
  let V:=put U a (some false)
  have routed:=grid.goR forward (by decide) room
  have one:=keep enter scan (D 9) (D 9+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [grid_blank grid 9 (by decide)];exact entry) rfl
  have pairs:=append_pairs (P:=P) ss sk rs rk (d+1) (a:=D 9+1) (by omega) busy
  have retreatOne:=keep scan take (D 9+1+2*(d+1)) (a+1) T .left (P:=P)
    (by omega) (by dsimp only [a];omega) ss (rn _ stop) (by change D 9+1+2*(d+1)-1=a+1;dsimp only [a];omega)
  have two:=hop take (flag b) (a+1) a T (some false) .left (P:=P) (by dsimp only [a];omega) (by dsimp only [a];omega) st
    (by rw [last];exact (reads b).1) (by change a+1-1=a;omega)
  have atFlag : U a=some true := by
    change (if a=a+1 then some false else T a)=some true
    rw [if_neg (by omega : a≠a+1)]
    have same : D 9+1+2*d=a := by dsimp only [a];omega
    rw [←same]
    exact (busy d (by omega)).1
  have three:=hop (flag b) (back b) a (a-1) U (some false) .left (P:=P)
    (by dsimp only [a];omega) (by dsimp only [a];omega) (safe b).1
    (by rw [atFlag];exact (reads b).2.1) rfl
  have g1 : Grid D U:=grid.change_some (a+1) b false last
  have g2 : Grid D V:=g1.change_some a true false atFlag
  have retreat:=sweepL (back b) V (D 9) (2*d) (P:=P) (by omega) (safe b).2 (by
    intro i lo hi;obtain ⟨x,hx⟩:=grid_cells g2 9 i (by decide) lo (by change i<D 10;omega)
    rw [hx];exact (reads b).2.2.1 x)
  have exit:=keep (back b) (ret b) (D 9) (D 9) V .stay (P:=P) (by omega) (by omega) (safe b).2
    (by rw [grid_blank g2 9 (by decide)];exact (reads b).2.2.2) rfl
  have tail:=g2.goL (reverse b) (by decide) room
  have total:=routed.append (one.append (pairs.append (retreatOne.append (two.append (three.append
    (retreat.append (exit.append tail)))))))
  have time : (D 9-D 0+9)+(1+(2*(d+1)+(1+(1+(1+(2*d+(1+(D 9-D 0+9))))))))=
      2*(D 9-D 0)+4*d+25 := by omega
  rw [time] at total
  exact total
end FullBodyClosure
