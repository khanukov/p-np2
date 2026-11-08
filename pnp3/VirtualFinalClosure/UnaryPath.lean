import VirtualFinalClosure.Geometry
namespace VirtualFinalClosure.UnaryPath
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong generic framed route term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique framed route interface {mod}/{key}"
/-- Tape-aware opaque-machine proof component for the ACTUAL frozen BE
phase's decrement macro. Every row premise is supplied by its concrete ROM. -/
private theorem decrement {M : UniformTM} (start scan last back yes no : Fin M.stateCount)
    (P base width value : Nat) (T : Nat → Option Bool)
    (rStart : M.step start none=(scan,none,.right))
    (rScan : M.step scan (some true)=(scan,some true,.right))
    (rEnd : ∀ b : Option Bool,b=none ∨ b=some false → M.step scan b=(last,b,.left))
    (rZero : M.step last none=(no,none,.stay))
    (rTake : M.step last (some true)=(back,some false,.left))
    (rBack : ∀ b : Bool,M.step back (some b)=(back,some b,.left))
    (rDone : M.step back none=(yes,none,.stay))
    (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (endBlank : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=M) P (2*value+3) (node start base T)
      (node (if value=0 then no else yes) base
        (if value=0 then T else put T (base+value) (some false))) := by
  have entry:=keep (M:=M) (P:=P) start scan base (base+1) T .right
    (by omega) (by omega) (by rw [sep];exact rStart) rfl
  have forward:=sweepR (M:=M) (P:=P) scan T (base+1) value (by omega) (by
    intro i lo hi
    have cellValue:T i=some true := (digits i (by omega) (by omega)).trans (congrArg some (decide_eq_true (by omega)))
    rw [cellValue];exact rScan)
  have atEnd : T (base+1+value)=none ∨ T (base+1+value)=some false := by
    by_cases full : value=width
    · left
      rw [show base+1+value=base+width+1 by omega]
      exact endBlank
    · right
      rw [digits _ (by omega) (by omega)]
      simp
  have turn:=keep (M:=M) (P:=P) scan last (base+1+value) (base+value) T .left
    (by omega) (by omega) (rEnd _ atEnd) (by dsimp only [dest];omega)
  have pathPrefix:=joinPath (joinPath entry forward) turn
  by_cases empty : value=0
  · subst value
    have ending:=keep (M:=M) (P:=P) last no base base T .stay
      (by omega) (by omega) (by rw [sep];exact rZero) rfl
    simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero,ite_true] using joinPath pathPrefix ending
  · have pos:0<value := by omega
    have cellValue:T (base+value)=some true := by
      rw [digits _ (by omega) (by omega)]
      simp only [le_refl,decide_true]
    have take:=hop (M:=M) (P:=P) last back (base+value) (base+(value-1)) T
      (some false) .left (by omega) (by omega) (by rw [cellValue];exact rTake) (by dsimp only [dest];omega)
    let U:=put T (base+value) (some false)
    have backPath:=sweepL (M:=M) (P:=P) back U base (value-1) (by omega) (by
      intro i lo hi
      have cellValue:T i=some true := (digits i lo (by omega)).trans (congrArg some (decide_eq_true (by omega)))
      have unchanged : U i=T i := by dsimp only [U,put];rw [if_neg (by omega)]
      rw [unchanged,cellValue];exact rBack true)
    have atBase:U base=none := by dsimp only [U,put];rw [if_neg (by omega),sep]
    have ending:=keep (M:=M) (P:=P) back yes base base U .stay
      (by omega) (by omega) (by rw [atBase];exact rDone) rfl
    have result:=joinPath (joinPath pathPrefix take) (joinPath backPath ending)
    simpa only [empty,ite_false,show 1+value+1+1+(value-1+1)=2*value+3 by omega] using result
/-- The same physically framed increment macro, including the genuine
full-bank cap. An occupied false cell is used only on the successful branch. -/
private theorem increment {M : UniformTM} (start scan back yes cap : Fin M.stateCount)
    (P base width value : Nat) (T : Nat → Option Bool)
    (rStart : M.step start none=(scan,none,.right))
    (rScan : M.step scan (some true)=(scan,some true,.right))
    (rPut : M.step scan (some false)=(back,some true,.left))
    (rCap : M.step scan none=(cap,none,.stay))
    (rBack : ∀ b : Bool,M.step back (some b)=(back,some b,.left))
    (rDone : M.step back none=(yes,none,.stay))
    (hv : value ≤ width) (fit : base+width+1 ≤ P)
    (sep : T base=none) (endBlank : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i ≤ base+value))) :
    GPath (M:=M) P (if value < width then 2*value+3 else value+2) (node start base T)
      (if value < width then node yes base (put T (base+value+1) (some true))
       else node cap (base+width+1) T) := by
  have enter:=keep (M:=M) (P:=P) start scan base (base+1) T .right
    (by omega) (by omega) (by rw [sep];exact rStart) rfl
  have forward:=sweepR (M:=M) (P:=P) scan T (base+1) value (by omega) (by
    intro i lo hi
    rw [(digits i (by omega) (by omega)).trans (congrArg some (decide_eq_true (by omega)))]
    exact rScan)
  have prefixPath:=joinPath enter forward
  by_cases space : value < width
  · rw [if_pos space,if_pos space]
    have cell : T (base+value+1)=some false:=by
      rw [digits _ (by omega) (by omega)]
      simp
    have write:=hop (M:=M) (P:=P) scan back (base+1+value) (base+value) T (some true) .left
      (by omega) (by omega) (by rw [show base+1+value=base+value+1 by omega,cell];exact rPut)
      (by dsimp only [dest];omega)
    let U:=put T (base+value+1) (some true)
    have turn : put T (base+1+value) (some true)=U:=by rw [show base+1+value=base+value+1 by omega]
    rw [turn] at write
    have returning:=sweepL (M:=M) (P:=P) back U base value (by omega) (by
      intro i lo hi
      have unchanged : U i=T i:=by dsimp only [U,put];rw [if_neg (by omega)]
      rw [unchanged,(digits i lo (by omega)).trans (congrArg some (decide_eq_true (by omega)))]
      exact rBack true)
    have blank : U base=none:=by dsimp only [U,put];rw [if_neg (by omega),sep]
    have ending:=keep (M:=M) (P:=P) back yes base base U .stay (by omega) (by omega)
      (by rw [blank];exact rDone) rfl
    convert joinPath (joinPath prefixPath write) (joinPath returning ending) using 1; omega
  · rw [if_neg space,if_neg space]
    have full : value=width:=by omega
    have ending:=keep (M:=M) (P:=P) scan cap (base+1+value) (base+width+1) T .stay
      (by omega) fit (by rw [show base+1+value=base+width+1 by omega,endBlank];exact rCap)
      (by dsimp only [dest];omega)
    convert joinPath prefixPath ending using 1; omega
#print axioms decrement
#print axioms increment
end VirtualFinalClosure.UnaryPath
