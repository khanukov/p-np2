import VirtualFinalClosure.GrowPaint
namespace VirtualFinalClosure.GrowReset
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("VirtualFinalClosure.GrowPaint","VirtualFinalClosure.GrowPaint","paint_bank","paintBank",1),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","outside","outside",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual six-bank reset interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual six-bank reset interface {mod}/{key}"
private def D (F r n j : Nat) : Nat := SerializedBody.delimiter F r n j
private def width (r n j : Nat) : Nat := if j=1 then n else r
private def stage (T : Nat  →  Option Bool) (F r n j : Nat) : Nat  →  Option Bool :=
  if j=0 then T else fun i=>
    if D F r n 0  <  i  ∧  i  <  D F r n 1 then some false else
    if D F r n 1  <  i  ∧  i  <  D F r n j then none else T i
private def cost (r n : Nat) : Nat  →  Nat
  | 0=>0
  | j+1=>cost r n j+width r n j+2
private def D_type : Nat  →  Nat  →  Nat  →  Nat  →  Nat := D
private def width_type : Nat  →  Nat  →  Nat  →  Nat := width
private def stage_type : (Nat  →  Option Bool)  →  Nat  →  Nat  →  Nat  →  Nat  →  Nat  →  Option Bool := stage
private def cost_type : Nat  →  Nat  →  Nat  →  Nat := cost
private theorem next (F r n j : Nat) (hj : j < 6) : D F r n (j+1)=D F r n j+width r n j+1 := by
  interval_cases j <;> norm_num [D,width,SerializedBody.delimiter] <;> omega
private theorem ordered (F r n j h : Nat) (jh : j ≤ h) (hh : h ≤ 6) : D F r n j ≤ D F r n h := by
  interval_cases h <;> interval_cases j <;> dsimp only [D,SerializedBody.delimiter] <;> omega
private theorem initial (T : Nat  →  Option Bool) (F r n : Nat) : stage T F r n 0=T := by rfl
private theorem above (T : Nat  →  Option Bool) (F r n j i : Nat) (hj : j ≤ 6)
    (hi : D F r n j ≤ i) : stage T F r n j i=T i := by
  by_cases zero : j=0
  · subst j;rfl
  · have pos : 1 ≤ j := by omega
    have lower:=ordered F r n 1 j pos hj
    dsimp only [stage]
    rw [if_neg zero,if_neg (by omega),if_neg (by omega)]
private theorem stage_add (T : Nat  →  Option Bool) (F r n j : Nat) (hj : j < 6)
    (blank : T (D F r n j)=none) :
    block (stage T F r n j) (D F r n j+1) (width r n j) (if j=0 then some false else none)=
      stage T F r n (j+1) := by
  have edge:=next F r n j hj
  have mono:=ordered F r n j (j+1) (by omega) (by omega)
  funext i
  by_cases zero : j=0
  · subst j
    have shape : D F r n 1=D F r n 0+r+1 := by dsimp only [D,SerializedBody.delimiter];omega
    dsimp only [stage,width]
    change (if D F r n 0+1 ≤ i  ∧  i < D F r n 0+1+r then some false else T i)=
      (if D F r n 0 < i  ∧  i < D F r n 1 then some false else if D F r n 1 < i  ∧  i < D F r n 1 then none else T i)
    rw [if_neg (by omega : ¬(D F r n 1 < i  ∧  i < D F r n 1))]
    have same : (D F r n 0+1 ≤ i  ∧  i < D F r n 0+1+r)  ↔  (D F r n 0 < i  ∧  i < D F r n 1) := by omega
    simp only [same]
  · have pos : 1 ≤ j := by omega
    have lower:=ordered F r n 1 j pos (by omega)
    have nextNonzero : j+1≠0 := by omega
    dsimp only [block,stage]
    rw [if_neg zero,if_neg nextNonzero,if_neg zero]
    by_cases first : D F r n 0 < i  ∧  i < D F r n 1
    · rw [if_pos first,if_pos first,if_neg (by omega)]
    · rw [if_neg first,if_neg first]
      by_cases earlier : i < D F r n j
      · rw [if_neg (by omega)]
        have same : (D F r n 1 < i  ∧  i < D F r n j)  ↔  (D F r n 1 < i  ∧  i < D F r n (j+1)) := by omega
        simp only [same]
      · by_cases atDelimiter : i=D F r n j
        · subst i
          rw [if_neg (by omega),if_neg (by omega),blank]
          split <;> rfl
        · by_cases last : i < D F r n (j+1)
          · rw [if_pos (by omega),if_pos (by omega)]
          · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
/-- Every reset microstep is a literal row of the FROZEN native table. The
occupied width-r bank0 becomes SomeFalse; all other five fields become NONE.
No source, assignment, fence, exterior or delimiter is rewritten by this stage. -/
private theorem reset (k P m F r n : Nat) (T : Nat  →  Option Bool) (hm : m < 144)
    (fit : D F r n 6 ≤ P)
    (blank : ∀ j,j ≤ 6  →  T (D F r n j)=none)
    (occupied : ∀ j,j < 6  →  ∀ i,D F r n j < i  →  i < D F r n (j+1)  →  ∃ b,T i=some b) :
    GPath (M:=machine k) P (n+5*r+12) (C k 52 m (D F r n 0) T)
      (C k 64 m (D F r n 6) (stage T F r n 6)) := by
  have loop (j : Nat) (hj : j ≤ 6) :
      GPath (M:=machine k) P (cost r n j) (C k 52 m (D F r n 0) T)
        (C k (52+2*j) m (D F r n j) (stage T F r n j)) := by
    induction j with
    | zero=>
      rw [initial]
      exact nilPath _ ((ordered F r n 0 6 (by omega) (by omega)).trans fit)
    | succ j ih=>
      have before:=ih (by omega)
      have edge:=next F r n j (by omega)
      let U:=stage T F r n j
      have start : U (D F r n j)=none := (above T F r n j _ (by omega) le_rfl).trans (blank j (by omega))
      have finish : U (D F r n j+width r n j+1)=none := by
        rw [←edge]
        exact (above T F r n j _ (by omega) (ordered F r n j (j+1) (by omega) (by omega))).trans (blank (j+1) (by omega))
      have cells : ∀ i,D F r n j < i  →  i < D F r n j+width r n j+1  →  ∃ b,U i=some b := by
        intro i lo hi
        change ∃ b,stage T F r n j i=some b
        rw [above T F r n j i (by omega) lo.le]
        exact occupied j (by omega) i lo (by rw [edge];exact hi)
      have field:=paintBank k P m j (D F r n j) (width r n j) U hm (by omega)
        (by rw [←edge];exact (ordered F r n (j+1) 6 (by omega) (by omega)).trans fit) start finish cells
      rw [←edge,stage_add T F r n j (by omega) (blank j (by omega))] at field
      have control : 54+2*j=52+2*(j+1) := by omega
      rw [control] at field
      have path:=joinPath before field
      change GPath (M:=machine k) P (cost r n j+width r n j+2) _ _
      convert path using 1
  have final:=loop 6 le_rfl
  have price : cost r n 6=n+5*r+12 := by norm_num [cost,width];omega
  rw [price] at final
  exact final
#print axioms D_type
#print axioms width_type
#print axioms stage_type
#print axioms cost_type
#print axioms next
#print axioms ordered
#print axioms initial
#print axioms above
#print axioms stage_add
#print axioms reset
end VirtualFinalClosure.GrowReset
