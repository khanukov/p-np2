import VirtualFinalClosure.Cells
namespace VirtualFinalClosure.Paths
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","embed","emb",0),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","executePath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pack",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat :=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong reused path/row kind {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique existing path/row interface {mod}/{key}"
private def cellTac (i : Nat) : TacticM Unit := do
  unless i<717 do throwError "Static cell index outside fixed ROM"
  let suffix:=if i<10 then "00"++toString i else if i<100 then "0"++toString i else toString i
  let entries:=(← getEnv).constants.toList.filter fun (n,_)=>
    n.toString.startsWith "_private.VirtualFinalClosure.Cells." &&
    n.toString.endsWith (".VirtualFinalClosure.Cells.cell_"++suffix)
  match entries with
  | [(n,.thmInfo ci)]=>
    logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
    evalTactic (← `(tactic| exact $(mkIdent n)))
  | _=>throwError "Nonunique kernel-certified literal ROM cell {i}"
private def nc (k q m : Nat) : Fin (machine k).stateCount :=
  pack k ((CertificateGuardClosure.machine k).stateCount+q) m
private def C (k q m h : Nat) (T : Nat → Option Bool) : GNode (machine k) :=
  node (nc k q m) h T
private theorem row6 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 6 m) none=(nc k 7 m,none,.right) := by
  have r:=literalRow k 6 m 7 0 2 0 none (by decide) hm (by decide) (by run_tac cellTac 18)
  rw [mode0 m hm] at r
  exact r
private theorem row7true (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 7 m) (some true)=(nc k 7 m,some true,.right) := by
  have r:=literalRow k 7 m 7 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 23)
  rw [mode0 m hm] at r
  exact r
private theorem row7end (k m : Nat) (hm : m<144) (b : Option Bool) (hb : b=none ∨ b=some false) :
    (machine k).step (nc k 7 m) b=(nc k 8 m,b,.left) := by
  rcases hb with rfl|rfl
  · have r:=literalRow k 7 m 8 0 0 0 none (by decide) hm (by decide) (by run_tac cellTac 21)
    rw [mode0 m hm] at r
    exact r
  · have r:=literalRow k 7 m 8 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 22)
    rw [mode0 m hm] at r
    exact r
private theorem row8zero (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 8 m) none=(nc k 31 m,none,.stay) := by
  have r:=literalRow k 8 m 31 0 1 0 none (by decide) hm (by decide) (by run_tac cellTac 24)
  rw [mode0 m hm] at r
  exact r
private theorem row8take (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 8 m) (some true)=(nc k 9 m,some false,.left) := by
  have r:=literalRow k 8 m 9 1 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 26)
  rw [mode0 m hm] at r
  exact r
private theorem row9back (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 9 m) (some b)=(nc k 9 m,some b,.left) := by
  cases b
  · have r:=literalRow k 9 m 9 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 28)
    rw [mode0 m hm] at r
    exact r
  · have r:=literalRow k 9 m 9 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 29)
    rw [mode0 m hm] at r
    exact r
private theorem row9done (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 9 m) none=(nc k 10 m,none,.stay) := by
  have r:=literalRow k 9 m 10 0 1 0 none (by decide) hm (by decide) (by run_tac cellTac 27)
  rw [mode0 m hm] at r
  exact r
/-- EXACT native markDec phase, including the empty counter. No new counter
machine is introduced: these are the frozen candidate's literal controls6..9. -/
private theorem mark_decrement (k P m base width value : Nat) (T : Nat → Option Bool)
    (hm : m<144) (hv : value≤width) (fit : base+width+1≤P)
    (sep : T base=none) (last : T (base+width+1)=none)
    (digits : ∀ i,base < i → i < base+width+1 → T i=some (decide (i≤base+value))) :
    GPath (M:=machine k) P (2*value+3) (C k 6 m base T)
      (C k (if value=0 then 31 else 10) m base
        (if value=0 then T else put T (base+value) (some false))) := by
  have entry:=keep (M:=machine k) (P:=P) (nc k 6 m) (nc k 7 m) base (base+1) T .right
    (by omega) (by omega) (by rw [sep];exact row6 k m hm) rfl
  have forward:=sweepR (M:=machine k) (P:=P) (nc k 7 m) T (base+1) value (by omega) (by
    intro i lo hi
    have cellValue:T i=some true := (digits i (by omega) (by omega)).trans (congrArg some (decide_eq_true (by omega)))
    rw [cellValue];exact row7true k m hm)
  have atEnd : T (base+1+value)=none ∨ T (base+1+value)=some false := by
    by_cases full : value=width
    · left
      rw [show base+1+value=base+width+1 by omega]
      exact last
    · right
      rw [digits _ (by omega) (by omega)]
      simp
  have turn:=keep (M:=machine k) (P:=P) (nc k 7 m) (nc k 8 m) (base+1+value) (base+value) T .left
    (by omega) (by omega) (row7end k m hm _ atEnd) (by dsimp only [dest];omega)
  have pathPrefix:=joinPath (joinPath entry forward) turn
  by_cases empty : value=0
  · subst value
    have ending:=keep (M:=machine k) (P:=P) (nc k 8 m) (nc k 31 m) base base T .stay
      (by omega) (by omega) (by rw [sep];exact row8zero k m hm) rfl
    simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero,ite_true] using joinPath pathPrefix ending
  · have pos:0<value := by omega
    have cellValue:T (base+value)=some true := by
      rw [digits _ (by omega) (by omega)]
      simp only [le_refl,decide_true]
    have take:=hop (M:=machine k) (P:=P) (nc k 8 m) (nc k 9 m) (base+value) (base+(value-1)) T
      (some false) .left (by omega) (by omega) (by rw [cellValue];exact row8take k m hm) (by dsimp only [dest];omega)
    let U:=put T (base+value) (some false)
    have back:=sweepL (M:=machine k) (P:=P) (nc k 9 m) U base (value-1) (by omega) (by
      intro i lo hi
      have cellValue:T i=some true := (digits i lo (by omega)).trans (congrArg some (decide_eq_true (by omega)))
      have unchanged : U i=T i := by dsimp only [U,put];rw [if_neg (by omega)]
      rw [unchanged,cellValue];exact row9back k m hm true)
    have atBase:U base=none := by dsimp only [U,put];rw [if_neg (by omega),sep]
    have ending:=keep (M:=machine k) (P:=P) (nc k 9 m) (nc k 10 m) base base U .stay
      (by omega) (by omega) (by rw [atBase];exact row9done k m hm) rfl
    have result:=joinPath (joinPath pathPrefix take) (joinPath back ending)
    simpa only [empty,ite_false,show 1+value+1+1+(value-1+1)=2*value+3 by omega] using result
#print axioms row6
#print axioms row7true
#print axioms row7end
#print axioms row8zero
#print axioms row8take
#print axioms row9back
#print axioms row9done
#print axioms mark_decrement
end VirtualFinalClosure.Paths
