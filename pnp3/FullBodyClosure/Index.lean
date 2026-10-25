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
-- Unary tape views are proof-side representations; no new runtime constructor.
private def counter (T : Nat → Option Bool) (D : Nat → Nat) (j v : Nat) : Nat → Option Bool :=
  fun i=>if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else T i
private theorem delimiter_out {D T} (g : Grid D T) {j k : Nat} (hj : j < 12) (hk : k ≤ 12) :
    ¬(D j < D k ∧ D k < D (j+1)) := by
  by_cases order : k ≤ j
  · have :=grid_mono g k j order (by omega);omega
  · have :=grid_mono g (j+1) k (by omega) hk;omega
private theorem counter_grid {D T} (g : Grid D T) (j v : Nat) (hj : j < 12) : Grid D (counter T D j v) := by
  apply grid_make (grid_rise g) (grid_mono g)
  · intro k hk
    simp only [counter,if_neg (delimiter_out g hj hk)]
    exact grid_blank g k hk
  · intro k i hk lo hi
    by_cases inside : D j < i ∧ i < D (j+1)
    · exact ⟨decide (i-D j ≤ v),by simp only [counter,if_pos inside]⟩
    · simp only [counter,if_neg inside];exact grid_cells g k i hk lo hi
private theorem counter_unary (T : Nat → Option Bool) (D : Nat → Nat) (j v : Nat) : Unary D (counter T D j v) j v := by
  intro i lo hi
  exact if_pos ⟨lo,hi⟩
private theorem counter_down (T : Nat → Option Bool) (D : Nat → Nat) (j v w : Nat)
    (len : D (j+1)=D j+w+1) (pos : 0 < v) (fit : v ≤ w) :
    put (counter T D j v) (D j+v) (some false)=counter T D j (v-1) := by
  funext i
  change (if i=D j+v then some false else counter T D j v i)=counter T D j (v-1) i
  by_cases eq : i=D j+v
  · have inside : D j < i ∧ i < D (j+1) := by omega
    have no : ¬ i-D j ≤ v-1 := by omega
    simp only [if_pos eq,counter,if_pos inside];simp [no]
  · rw [if_neg eq]
    by_cases inside : D j < i ∧ i < D (j+1)
    · simp only [counter,if_pos inside]
      by_cases bound : i-D j ≤ v-1
      · have bound' : i-D j ≤ v := by omega
        simp [bound,bound']
      · have bound' : ¬ i-D j ≤ v := by omega
        simp [bound,bound']
    · simp only [counter,if_neg inside]
private theorem counter_up (T : Nat → Option Bool) (D : Nat → Nat) (j v w : Nat)
    (len : D (j+1)=D j+w+1) (fit : v < w) :
    put (counter T D j v) (D j+v+1) (some true)=counter T D j (v+1) := by
  funext i
  change (if i=D j+v+1 then some true else counter T D j v i)=counter T D j (v+1) i
  by_cases eq : i=D j+v+1
  · have inside : D j < i ∧ i < D (j+1) := by omega
    have yes : i-D j ≤ v+1 := by omega
    simp only [if_pos eq,counter,if_pos inside];simp [yes]
  · rw [if_neg eq]
    by_cases inside : D j < i ∧ i < D (j+1)
    · simp only [counter,if_pos inside]
      by_cases bound : i-D j ≤ v
      · have bound' : i-D j ≤ v+1 := by omega
        simp [bound,bound']
      · have bound' : ¬ i-D j ≤ v+1 := by omega
        simp [bound,bound']
    · simp only [counter,if_neg inside]
private theorem counter_put_outside (T : Nat → Option Bool) (D : Nat → Nat) (j v h : Nat) (b : Option Bool)
    (outside : ¬(D j < h ∧ h < D (j+1))) :
    put (counter T D j v) h b=counter (put T h b) D j v := by
  funext i
  change (if i=h then b else counter T D j v i)=counter (fun x=>if x=h then b else T x) D j v i
  by_cases eq : i=h
  · subst i;simp only [counter,if_neg outside]
  · simp only [if_neg eq,counter]
private def StrictIncRows (j : Nat) (start out abort : Fin 7500) : Prop :=
  ∃ e scan check back ok failed : Fin 7500,
    4 ≤ e.val ∧ 4 ≤ scan.val ∧ 4 ≤ check.val ∧ 4 ≤ back.val ∧
    RouteR 0 j start e ∧ RouteL j 0 ok out ∧ RouteL (j+1) 0 failed abort ∧
    SerializedBody.machine.step e none=(scan,none,.right) ∧
    SerializedBody.machine.step scan (some true)=(scan,some true,.right) ∧
    SerializedBody.machine.step scan (some false)=(check,some true,.right) ∧
    SerializedBody.machine.step scan none=(failed,none,.stay) ∧
    (∀ b,SerializedBody.machine.step check (some b)=(back,some b,.left)) ∧
    SerializedBody.machine.step check none=(failed,none,.stay) ∧
    (∀ b,SerializedBody.machine.step back (some b)=(back,some b,.left)) ∧
    SerializedBody.machine.step back none=(ok,none,.stay)
private theorem strict_inc_success {D T j w v P start out abort} (grid : Grid D T)
    (hj : j < 12) (fit : D 12 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j v) (small : v+1 < w) (code : StrictIncRows j start out abort) :
    Path P (2*(D j-D 0+j)+2*v+5) (node start (D 0) T)
      (node out (D 0) (put T (D j+v+1) (some true))) := by
  rcases code with ⟨e,scan,check,back,ok,failed,se,ss,sc,sb,route,ret,_,re,rs,rt,_,rc,_,rl,rn⟩
  have inRoom : D j+v+2 ≤ P := le_trans (by rw [len];omega)
    (le_trans (grid_mono grid (j+1) 12 (by omega) (by omega)) fit)
  have val : T (D j+v+1)=some false := by
    rw [unary _ (by omega) (by omega)]
    simp [show ¬ D j+v+1-D j ≤ v by omega]
  let U:=put T (D j+v+1) (some true)
  have gu : Grid D U:=grid.change_some _ false true val
  obtain ⟨nextBit,next⟩:=grid_cells gu j (D j+v+2) hj (by omega) (by omega)
  have entry:=keep e scan (D j) (D j+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [grid_blank grid j (by omega)];exact re) rfl
  have sweep:=sweepR scan T (D j+1) v (P:=P) (by omega) ss (by
    intro i lo hi;rw [unary_true unary len (by omega) (by omega) (by omega)];exact rs)
  rw [show D j+1+v=D j+v+1 by omega] at sweep
  have take:=hop scan check (D j+v+1) (D j+v+2) T (some true) .right (P:=P) (by omega) inRoom ss
    (by rw [val];exact rt) rfl
  have checked:=keep check back (D j+v+2) (D j+v+1) U .left (P:=P) inRoom (by omega) sc
    (by rw [next];exact rc nextBit) (by change D j+v+2-1=D j+v+1;omega)
  have retreat:=sweepL back U (D j) (v+1) (P:=P) (by omega) sb (by
    intro i lo hi;obtain ⟨b,hb⟩:=grid_cells gu j i hj lo (by omega);rw [hb];exact rl b)
  rw [show D j+(v+1)=D j+v+1 by omega] at retreat
  have exit:=keep back ok (D j) (D j) U .stay (P:=P) (by omega) (by omega) sb
    (by rw [grid_blank gu j (by omega)];exact rn) rfl
  have total:=(grid.goR route (by omega) fit).append
    (entry.append (sweep.append (take.append (checked.append (retreat.append (exit.append (gu.goL ret (by omega) fit)))))))
  have time : (D j-D 0+(j-0))+(1+(v+(1+(1+(v+1+(1+(D j-D 0+(j-0))))))))=
      2*(D j-D 0+j)+2*v+5 := by omega
  rw [time] at total
  exact total
private theorem strict_inc_hits_cap {D T j w v P start out abort} (grid : Grid D T)
    (hj : j < 12) (fit : D 12 ≤ P) (len : D (j+1)=D j+w+1)
    (unary : Unary D T j v) (full : v+1=w) (code : StrictIncRows j start out abort) :
    Path P ((D j-D 0+j)+(v+3)+(D (j+1)-D 0+(j+1))) (node start (D 0) T)
      (node abort (D 0) (put T (D j+v+1) (some true))) := by
  rcases code with ⟨e,scan,check,back,ok,failed,se,ss,sc,_,route,_,ret,re,rs,rt,_,_,rc,_,_⟩
  have inRoom : D (j+1) ≤ P:=le_trans (grid_mono grid (j+1) 12 (by omega) (by omega)) fit
  have val : T (D j+v+1)=some false := by
    rw [unary _ (by omega) (by omega)]
    simp [show ¬ D j+v+1-D j ≤ v by omega]
  let U:=put T (D j+v+1) (some true)
  have gu : Grid D U:=grid.change_some _ false true val
  have entry:=keep e scan (D j) (D j+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [grid_blank grid j (by omega)];exact re) rfl
  have sweep:=sweepR scan T (D j+1) v (P:=P) (by omega) ss (by
    intro i lo hi;rw [unary_true unary len (by omega) (by omega) (by omega)];exact rs)
  rw [show D j+1+v=D j+v+1 by omega] at sweep
  have take:=hop scan check (D j+v+1) (D (j+1)) T (some true) .right (P:=P) (by omega) inRoom ss
    (by rw [val];exact rt) (by change D j+v+1+1=D (j+1);omega)
  have checked:=keep check failed (D (j+1)) (D (j+1)) U .stay (P:=P) inRoom inRoom sc
    (by rw [grid_blank gu (j+1) (by omega)];exact rc) rfl
  have total:=(grid.goR route (by omega) fit).append (entry.append (sweep.append (take.append (checked.append (gu.goL ret (by omega) fit)))))
  have time : (D j-D 0+(j-0))+(1+(v+(1+(1+(D (j+1)-D 0+(j+1-0))))))=
      (D j-D 0+j)+(v+3)+(D (j+1)-D 0+(j+1)) := by omega
  rw [time] at total
  exact total
private def address (v : Nat) : Fin 7500 := ⟨v%7500,Nat.mod_lt _ (by decide)⟩
private def hornerState (m : Fin 3) (b : Bool) : Fin 7500 :=
  address (#[2830,5217,7284,2931,5318,7385][3*(if b then 1 else 0)+m.val]!)
private def transferState (m : Fin 3) : Fin 7500 := address (#[2973,5360,7427][m.val]!)
private def foldState (m : Fin 3) : Fin 7500 := address (#[2763,5150,7217][m.val]!)
private def HornerRows (m : Fin 3) (b : Bool) : Prop :=
  ∃ dec zeroBranch first second : Fin 7500,
    4 ≤ (hornerState m b).val ∧
    SerializedBody.machine.step (hornerState m b) none=(dec,none,.stay) ∧
    DecRows 1 dec zeroBranch first ∧
    StrictIncRows 8 first second (SerializedBodyRefinement.getAbort m) ∧
    StrictIncRows 8 second (hornerState m b) (SerializedBodyRefinement.getAbort m) ∧
    (if b then StrictIncRows 8 zeroBranch (transferState m) (SerializedBodyRefinement.getAbort m) else zeroBranch=transferState m)
private def TransferRows (m : Fin 3) : Prop :=
  ∃ dec inc : Fin 7500,4 ≤ (transferState m).val ∧
    SerializedBody.machine.step (transferState m) none=(dec,none,.stay) ∧
    DecRows 8 dec (foldState m) inc ∧ IncRows 1 inc (transferState m)
end FullBodyClosure
