import VirtualFinalClosure.ModeRows
namespace VirtualFinalClosure.SourceShift
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","find_first","findFirst",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","find_later","findLater",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","carried_write","carriedWrite",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","changedBound",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","literal_row","literalRow",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","op0","mode0",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","cellTac","cellTac",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
private theorem row18_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 18 m) (none)=(nc k 21 m,none,.left) := by
  have rr:=literalRow k 18 m 21 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 54)
  rw [mode0 m hm] at rr
  exact rr
private theorem row19_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 19 m) (none)=(nc k 20 m,none,.left) := by
  have rr:=literalRow k 19 m 20 0 0 0 (none) (by decide) hm (by decide) (by run_tac cellTac 57)
  rw [mode0 m hm] at rr
  exact rr
private theorem row20_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 20 m) (none)=(nc k 21 m,none,.stay) := by
  have rr:=literalRow k 20 m 21 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 60)
  rw [mode0 m hm] at rr
  exact rr
private theorem row20_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 20 m) (some false)=(nc k 20 m,some false,.left) := by
  have rr:=literalRow k 20 m 20 1 0 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 61)
  rw [mode0 m hm] at rr
  exact rr
private theorem row20_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 20 m) (some true)=(nc k 20 m,some true,.left) := by
  have rr:=literalRow k 20 m 20 2 0 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 62)
  rw [mode0 m hm] at rr
  exact rr
private theorem row21_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 21 m) (some false)=(nc k 23 (changeMode 1 m),none,.right) := by
  have rr:=literalRow k 21 m 23 0 2 1 (some false) (by decide) hm (by decide) (by run_tac cellTac 64)
  exact rr
private theorem row21_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 21 m) (some true)=(nc k 23 (changeMode 2 m),none,.right) := by
  have rr:=literalRow k 21 m 23 0 2 2 (some true) (by decide) hm (by decide) (by run_tac cellTac 65)
  exact rr
private theorem row22_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 22 m) (some false)=(nc k 23 (changeMode 1 m),none,.right) := by
  have rr:=literalRow k 22 m 23 0 2 1 (some false) (by decide) hm (by decide) (by run_tac cellTac 67)
  exact rr
private theorem row22_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 22 m) (some true)=(nc k 23 (changeMode 2 m),none,.right) := by
  have rr:=literalRow k 22 m 23 0 2 2 (some true) (by decide) hm (by decide) (by run_tac cellTac 68)
  exact rr
private theorem row23_0 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 23 m) (none)=(nc k 24 m,none,.stay) := by
  have rr:=literalRow k 23 m 24 0 1 0 (none) (by decide) hm (by decide) (by run_tac cellTac 69)
  rw [mode0 m hm] at rr
  exact rr
private theorem row23_1 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 23 m) (some false)=(nc k 23 m,some false,.right) := by
  have rr:=literalRow k 23 m 23 1 2 0 (some false) (by decide) hm (by decide) (by run_tac cellTac 70)
  rw [mode0 m hm] at rr
  exact rr
private theorem row23_2 (k m : Nat) (hm : m<144) :
    (machine k).step (nc k 23 m) (some true)=(nc k 23 m,some true,.right) := by
  have rr:=literalRow k 23 m 23 2 2 0 (some true) (by decide) hm (by decide) (by run_tac cellTac 71)
  rw [mode0 m hm] at rr
  exact rr
private theorem row21_0 (k m : Nat) (b : Bool) (hm : m<144)
    (bit : sourceMode m=(if b then 1 else 0)) :
    (machine k).step (nc k 21 m) none=(nc k 22 m,some b,.left) := by
  have rr:=literalRow k 21 m 22 3 0 0 none (by decide) hm (by decide) (by run_tac cellTac 63)
  rw [mode0 m hm,carriedWrite m b bit] at rr
  exact rr
private theorem row21 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 21 m) (some b)=
      (nc k 23 (changeMode (if b then 2 else 1) m),none,.right) := by
  cases b
  · exact row21_1 k m hm
  · exact row21_2 k m hm
private theorem row22 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 22 m) (some b)=
      (nc k 23 (changeMode (if b then 2 else 1) m),none,.right) := by
  cases b
  · exact row22_1 k m hm
  · exact row22_2 k m hm
private theorem row20 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 20 m) (some b)=(nc k 20 m,some b,.left) := by
  cases b
  · exact row20_1 k m hm
  · exact row20_2 k m hm
private theorem row23 (k m : Nat) (hm : m<144) (b : Bool) :
    (machine k).step (nc k 23 m) (some b)=(nc k 23 m,some b,.right) := by
  cases b
  · exact row23_1 k m hm
  · exact row23_2 k m hm
private theorem mode_bound (op m : Nat) : changeMode op m<144 := by
  exact changedBound op m
/-- First paid source cell is read from actual EOF, not a proof-installed bit.
Exactly four literal rows, whole tape changes only by the selected source hole. -/
private theorem first_cell (k P m S : Nat) (T : Nat → Option Bool) (b : Bool)
    (hm : m<144) (eof : sourceMode m=2) (positive : 0<S) (fit : S≤P)
    (endBlank : T S=none) (selected : T (S-1)=some b) :
    GPath (M:=machine k) P 4 (C k 17 m S T)
      (C k 24 (changeMode (if b then 2 else 1) m) S (put T (S-1) none)) := by
  have p1:=keep (M:=machine k) (P:=P) (nc k 17 m) (nc k 18 m) S S T .stay
    fit fit (by rw [endBlank];exact findFirst k m hm eof) rfl
  have p2:=keep (M:=machine k) (P:=P) (nc k 18 m) (nc k 21 m) S (S-1) T .left
    fit (by omega) (by rw [endBlank];exact row18_0 k m hm) rfl
  have p3:=hop (M:=machine k) (P:=P) (nc k 21 m) (nc k 23 (changeMode (if b then 2 else 1) m))
    (S-1) S T none .right (by omega) fit (by rw [selected];exact row21 k m hm b)
    (by change S-1+1=S;omega)
  let U:=put T (S-1) none
  have atEnd : U S=none := by dsimp only [U,put];rw [if_neg (by omega),endBlank]
  have p4:=keep (M:=machine k) (P:=P) (nc k 23 (changeMode (if b then 2 else 1) m))
    (nc k 24 (changeMode (if b then 2 else 1) m)) S S U .stay
    fit fit (by rw [atEnd];exact row23_0 k _ (mode_bound _ _)) rfl
  exact joinPath (joinPath (joinPath p1 p2) p3) p4
/-- A later round restores the old lifted cell, moves one cell LEFT, and lifts
its actual Bool. The occupied suffix is traversed literally in both directions. -/
private theorem previous_cell (k P m S h : Nat) (T : Nat → Option Bool) (oldBit b : Bool)
    (hm : m<144) (mode : sourceMode m=(if oldBit then 1 else 0))
    (positive : 0<h) (inside : h<S) (fit : S≤P)
    (endBlank : T S=none) (hole : T h=none) (selected : T (h-1)=some b)
    (suffix : ∀ i, h < i → i < S → ∃ bit,T i=some bit) :
    GPath (M:=machine k) P (2*(S-h)+5) (C k 17 m S T)
      (C k 24 (changeMode (if b then 2 else 1) m) S
        (put (put T h (some oldBit)) (h-1) none)) := by
  have occupied : sourceMode m≠2 := by rw [mode];cases oldBit <;> decide
  have p1:=keep (M:=machine k) (P:=P) (nc k 17 m) (nc k 19 m) S S T .stay
    fit fit (by rw [endBlank];exact findLater k m hm occupied) rfl
  have p2:=keep (M:=machine k) (P:=P) (nc k 19 m) (nc k 20 m) S (S-1) T .left
    fit (by omega) (by rw [endBlank];exact row19_0 k m hm) rfl
  have search:=sweepL (M:=machine k) (P:=P) (nc k 20 m) T h (S-h-1) (by omega) (by
    intro i lo hi
    obtain ⟨bit,cell⟩:=suffix i lo (by omega)
    rw [cell];exact row20 k m hm bit)
  rw [show h+(S-h-1)=S-1 by omega] at search
  have p3:=keep (M:=machine k) (P:=P) (nc k 20 m) (nc k 21 m) h h T .stay
    (by omega) (by omega) (by rw [hole];exact row20_0 k m hm) rfl
  have p4:=hop (M:=machine k) (P:=P) (nc k 21 m) (nc k 22 m) h (h-1) T (some oldBit) .left
    (by omega) (by omega) (by rw [hole];exact row21_0 k m oldBit hm mode) rfl
  let U:=put T h (some oldBit)
  have prev : U (h-1)=some b := by dsimp only [U,put];rw [if_neg (by omega),selected]
  have p5:=hop (M:=machine k) (P:=P) (nc k 22 m) (nc k 23 (changeMode (if b then 2 else 1) m))
    (h-1) h U none .right (by omega) (by omega) (by rw [prev];exact row22 k m hm b)
    (by change h-1+1=h;omega)
  let V:=put U (h-1) none
  have back:=sweepR (M:=machine k) (P:=P) (nc k 23 (changeMode (if b then 2 else 1) m)) V h (S-h)
    (by omega) (by
      intro i lo hi
      by_cases atHole : i=h
      · subst i
        have cell : V h=some oldBit := by dsimp only [V,U,put];rw [if_neg (by omega),if_pos rfl]
        rw [cell];exact row23 k _ (mode_bound _ _) oldBit
      · obtain ⟨bit,cell⟩:=suffix i (by omega) (by omega)
        have eq : V i=T i := by dsimp only [V,U,put];rw [if_neg (by omega),if_neg atHole]
        rw [eq,cell];exact row23 k _ (mode_bound _ _) bit)
  rw [show h+(S-h)=S by omega] at back
  have atEnd : V S=none := by dsimp only [V,U,put];rw [if_neg (by omega),if_neg (by omega),endBlank]
  have p6:=keep (M:=machine k) (P:=P) (nc k 23 (changeMode (if b then 2 else 1) m))
    (nc k 24 (changeMode (if b then 2 else 1) m)) S S V .stay
    fit fit (by rw [atEnd];exact row23_0 k _ (mode_bound _ _)) rfl
  have combined:=joinPath (joinPath (joinPath (joinPath (joinPath (joinPath (joinPath p1 p2) search) p3) p4) p5) back) p6
  rw [show 1+1+(S-h-1)+1+1+1+(S-h)+1=2*(S-h)+5 by omega] at combined
  exact combined
#print axioms first_cell
#print axioms previous_cell
end VirtualFinalClosure.SourceShift
