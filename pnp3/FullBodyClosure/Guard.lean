import FullBodyClosure.Control
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1
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
private abbrev node : Fin 7500 → Nat → (Nat → Option Bool) → Node := by run_tac checkedKernel "Node.mk"
private abbrev nodeHead : Node → Nat := by run_tac checkedKernel "Node.head"
private abbrev put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by run_tac checkedKernel "put"
private abbrev dest : Nat → Move → Nat := by run_tac checkedKernel "dest"
private theorem Path.append : ∀ {P t u c d e} (_h : Path P t c d) (_g : Path P u d e),
    Path P (t+u) c e := by run_tac checkedKernel "Path.append"
private theorem keep : ∀ {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (_hb : h  ≤  P) (_ha : h'  ≤  P)
    (_safe : 4  ≤  s.val)
    (_row : SerializedBody.machine.step s (T h) = (s',T h,m)) (_hm : dest h m=h'),
    Path P 1 (node (s) (h) (T)) (node (s') (h') (T)) := by run_tac checkedKernel "keep"
private theorem Grid.goR : ∀ {D T i j s q P} (_g : Grid D T) (_r : RouteR i j s q)
    (_hj : j  ≤  12) (_fit : D 12  ≤  P),
    Path P (D j-D i+(j-i)) (node (s) (D i) (T)) (node (q) (D j) (T)) := by run_tac checkedKernel "Grid.goR"
private theorem Grid.goL : ∀ {D T i j s q P} (_g : Grid D T) (_r : RouteL i j s q)
    (_hi : i  ≤  12) (_fit : D 12  ≤  P),
    Path P (D i-D j+(i-j)) (node (s) (D i) (T)) (node (q) (D j) (T)) := by run_tac checkedKernel "Grid.goL"
private theorem grid_mono : ∀ {D T}, Grid D T → ∀ a b,a  ≤  b → b  ≤  12 → D a  ≤  D b := by run_tac checkedKernel "Grid.mono"
private theorem grid_blank : ∀ {D T}, Grid D T → ∀ j,j  ≤  12 → T (D j)=none := by run_tac checkedKernel "Grid.blank"
private theorem grid_cells : ∀ {D T}, Grid D T → ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b := by run_tac checkedKernel "Grid.cells"
private theorem rnil : ∀ i q,RouteR i i q q := by run_tac checkedKernel "RouteR.nil"
private theorem lnil : ∀ i q,RouteL i i q q := by run_tac checkedKernel "RouteL.nil"
private theorem rnext : ∀ {i j e s q x}, 4  ≤  e.val → 4  ≤  s.val →
    SerializedBody.machine.step e none=(s,none,.right) →
    (∀ b,SerializedBody.machine.step s (some b)=(s,some b,.right)) →
    SerializedBody.machine.step s none=(q,none,.stay) → RouteR (i+1) j q x → RouteR i j e x := by run_tac checkedKernel "RouteR.next"
private theorem lnext : ∀ {i j e s q x}, 4  ≤  e.val → 4  ≤  s.val →
    SerializedBody.machine.step e none=(s,none,.left) →
    (∀ b,SerializedBody.machine.step s (some b)=(s,some b,.left)) →
    SerializedBody.machine.step s none=(q,none,.stay) → RouteL i j q x → RouteL (i+1) j e x := by run_tac checkedKernel "RouteL.next"

private def GuardRows (start good bad : Fin 7500) : Prop :=
  ∃ route enter scan back pos neg : Fin 7500,
    4 ≤ start.val ∧ 4 ≤ enter.val ∧ 4 ≤ scan.val ∧ 4 ≤ back.val ∧
    SerializedBody.machine.step start none=(route,none,.stay) ∧
    RouteR 0 1 route enter ∧ RouteL 1 0 pos good ∧ RouteL 2 0 neg bad ∧
    SerializedBody.machine.step enter none=(scan,none,.right) ∧
    SerializedBody.machine.step scan none=(neg,none,.stay) ∧
    (∀ b,SerializedBody.machine.step scan (some b)=(back,some b,.stay)) ∧
    (∀ b,SerializedBody.machine.step back (some b)=(back,some b,.left)) ∧
    SerializedBody.machine.step back none=(pos,none,.stay)
private theorem guard_run {D T P n start good bad} (grid : Grid D T) (room : D 12 ≤ P)
    (len : D 2=D 1+n+1) (code : GuardRows start good bad) :
    ∃ t,t ≤ 16*(P+1) ∧ Path P t (node start (D 0) T) (node (if n=0 then bad else good) (D 0) T) := by
  rcases code with ⟨route,enter,scan,back,pos,neg,ss,se,sc,sb,jump,forward,reverse,emptyRoute,entry,empty,nonempty,left,exit⟩
  have rootFit : D 0 ≤ P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) room
  have bank2:=grid_mono grid 2 12 (by decide) (by decide)
  have order:=grid_mono grid 0 1 (by decide) (by decide)
  have one:=keep start route (D 0) (D 0) T .stay (P:=P) rootFit rootFit ss
    (by rw [grid_blank grid 0 (by decide)];exact jump) rfl
  have routed:=grid.goR forward (by decide) room
  have two:=keep enter scan (D 1) (D 1+1) T .right (P:=P) (by omega) (by omega) se
    (by rw [grid_blank grid 1 (by decide)];exact entry) rfl
  by_cases zero : n=0
  · have atRight : D 1+1=D 2:=by omega
    have three:=keep scan neg (D 1+1) (D 2) T .stay (P:=P) (by omega) (by omega) sc
      (by rw [atRight,grid_blank grid 2 (by decide)];exact empty) (by change D 1+1=D 2;exact atRight)
    have tail:=grid.goL emptyRoute (by decide) room
    have path:=one.append (routed.append (two.append (three.append tail)))
    rw [if_pos zero]
    refine ⟨_,?_,path⟩
    omega
  · obtain ⟨b,cell⟩:=grid_cells grid 1 (D 1+1) (by decide) (by omega) (by change D 1+1 < D 2;omega)
    have three:=keep scan back (D 1+1) (D 1+1) T .stay (P:=P) (by omega) (by omega) sc
      (by rw [cell];exact nonempty b) rfl
    have four:=keep back back (D 1+1) (D 1) T .left (P:=P) (by omega) (by omega) sb
      (by rw [cell];exact left b) rfl
    have five:=keep back pos (D 1) (D 1) T .stay (P:=P) (by omega) (by omega) sb
      (by rw [grid_blank grid 1 (by decide)];exact exit) rfl
    have tail:=grid.goL reverse (by decide) room
    have path:=one.append (routed.append (two.append (three.append (four.append (five.append tail)))))
    rw [if_neg zero]
    refine ⟨_,?_,path⟩
    omega
private def st (q : Nat) : Fin 7500 := ⟨q%7500,Nat.mod_lt _ (by decide)⟩
section LiteralRows
set_option maxRecDepth 4000
private theorem guardCode0 : GuardRows (st 2226) (st 2283) (st 270) := by
  exact ⟨(st 2225),(st 2223),(st 2222),(st 2221),(st 2220),(st 288),by decide,by decide,by decide,by decide,rfl,(rnext (s:=(st 2224)) (q:=(st 2223)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 2223))),(lnext (s:=(st 2219)) (q:=(st 2283)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 2283))),(lnext (s:=(st 287)) (q:=(st 286)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnext (s:=(st 285)) (q:=(st 270)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 270)))),rfl,rfl,(by intro x;cases x <;> rfl),(by intro x;cases x <;> rfl),rfl⟩
private theorem guardCode1 : GuardRows (st 4842) (st 4899) (st 3307) := by
  exact ⟨(st 4841),(st 4839),(st 4838),(st 4837),(st 4836),(st 2344),by decide,by decide,by decide,by decide,rfl,(rnext (s:=(st 4840)) (q:=(st 4839)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 4839))),(lnext (s:=(st 4835)) (q:=(st 4899)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 4899))),(lnext (s:=(st 2343)) (q:=(st 2342)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnext (s:=(st 2341)) (q:=(st 3307)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 3307)))),rfl,rfl,(by intro x;cases x <;> rfl),(by intro x;cases x <;> rfl),rfl⟩
private theorem guardCode2 : GuardRows (st 6943) (st 7000) (st 5685) := by
  exact ⟨(st 6942),(st 6940),(st 6939),(st 6938),(st 6937),(st 2405),by decide,by decide,by decide,by decide,rfl,(rnext (s:=(st 6941)) (q:=(st 6940)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 6940))),(lnext (s:=(st 6936)) (q:=(st 7000)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 7000))),(lnext (s:=(st 2404)) (q:=(st 2403)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnext (s:=(st 2402)) (q:=(st 5685)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 5685)))),rfl,rfl,(by intro x;cases x <;> rfl),(by intro x;cases x <;> rfl),rfl⟩
end LiteralRows
end FullBodyClosure
