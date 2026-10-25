import VirtualFinalClosure.GuardForwardRows
import VirtualFinalClosure.GuardFlags
namespace VirtualFinalClosure.GuardForward
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","flag_preserved","flagPreserved",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","bad_preserved","badPreserved",1),
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",2),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","dispatch","dispatch",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","restore","restore",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","lift","lift",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row166_0","row166_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row167_0","row167_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row168_0","row168_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row168","row168",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row170_0","row170_0",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row171","row171",1),
      ("VirtualFinalClosure.GuardForwardRows","VirtualFinalClosure.GuardForwardRows","row171_0","row171_0",1),
      ("VirtualFinalClosure.ModeRows","VirtualFinalClosure.ModeRows","lifted_mode","liftedMode",1),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","modeBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","encodeMeta","encodeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
/-- Sticky EOF consumes only real terminal stays. No register/scratch bit is read. -/
private theorem eof (k P m S : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (mode : sourceMode m=2) (fit : S ≤ P) (blank : T S=none) :
    GPath (M:=machine k) P 2 (C k 165 m S T) (C k 172 m S T) := by
  have first:=keep (M:=machine k) (P:=P) (nc k 165 m) (nc k 166 m) S S T .stay
    fit fit (by rw [blank];simpa only [mode,if_pos rfl] using dispatch k m hm) rfl
  have last:=keep (M:=machine k) (P:=P) (nc k 166 m) (nc k 172 m) S S T .stay
    fit fit (by rw [blank];exact row166_0 k m hm) rfl
  exact joinPath first last
private theorem next (k P m S h : Nat) (T : Nat → Option Bool) (oldBit bit : Bool)
    (hm : m < 144) (mode : sourceMode m=(if oldBit then 1 else 0))
    (inside : h < S) (fit : S ≤ P) (endBlank : T S=none) (hole : T h=none)
    (selected : h+1 < S → T (h+1)=some bit)
    (suffix : ∀ i,h < i → i < S → ∃ b,T i=some b) :
    ∃ m',m' < 144 ∧ sourceMode m'=(if h+1=S then 2 else if bit then 1 else 0) ∧
      flag m'=flag m ∧ bad m'=bad m ∧ GPath (M:=machine k) P (2*(S-h)+3) (C k 165 m S T)
        (C k 172 m' S
          (if h+1=S then put T h (some oldBit)
           else put (put T h (some oldBit)) (h+1) none)) := by
  have occupied : sourceMode m≠2:=by rw [mode];cases oldBit <;> decide
  have enter:=keep (M:=machine k) (P:=P) (nc k 165 m) (nc k 167 m) S S T .stay
    fit fit (by rw [endBlank];simpa only [if_neg occupied] using dispatch k m hm) rfl
  have left:=keep (M:=machine k) (P:=P) (nc k 167 m) (nc k 168 m) S (S-1) T .left
    fit (by omega) (by rw [endBlank];exact row167_0 k m hm) rfl
  have search:=sweepL (M:=machine k) (P:=P) (nc k 168 m) T h (S-h-1) (by omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=suffix i lo (by omega)
    rw [cell];exact row168 k m hm b)
  rw [show h+(S-h-1)=S-1 by omega] at search
  have found:=keep (M:=machine k) (P:=P) (nc k 168 m) (nc k 169 m) h h T .stay
    (by omega) (by omega) (by rw [hole];exact row168_0 k m hm) rfl
  have restored:=hop (M:=machine k) (P:=P) (nc k 169 m) (nc k 170 m) h (h+1) T (some oldBit) .right
    (by omega) (by omega) (by rw [hole];exact restore k m hm oldBit mode) rfl
  let U:=put T h (some oldBit)
  have initial:=joinPath (joinPath (joinPath (joinPath enter left) search) found) restored
  by_cases atEOF : h+1=S
  · have last:=keep (M:=machine k) (P:=P) (nc k 170 m) (nc k 172 (changeMode 3 m)) S S U .stay
      fit fit (by
        have cell : U S=none:=by dsimp only [U,put];rw [if_neg (by omega),endBlank]
        rw [cell];exact row170_0 k m hm) rfl
    rw [atEOF] at initial
    refine ⟨changeMode 3 m,modeBound 3 m,?_,flagPreserved 3 m hm,badPreserved 3 m hm (by decide) (by decide),?_⟩
    · rw [if_pos atEOF]
      dsimp only [changeMode,sourceMode,encodeMeta,flag,phase,seen,bad]
      omega
    · have combined:=joinPath initial last
      rw [show 1+1+(S-h-1)+1+1+1=2*(S-h)+3 by omega] at combined
      simpa only [if_pos atEOF,U] using combined
  · have nextInside : h+1 < S:=by omega
    have selectedU : U (h+1)=some bit:=by dsimp only [U,put];rw [if_neg (by omega),selected nextInside]
    have lifted:=hop (M:=machine k) (P:=P) (nc k 170 m)
      (nc k 171 (changeMode (if bit then 2 else 1) m)) (h+1) (h+2) U none .right
      (by omega) (by omega) (by rw [selectedU];exact lift k m hm bit) rfl
    let V:=put U (h+1) none
    have returnPath:=sweepR (M:=machine k) (P:=P)
      (nc k 171 (changeMode (if bit then 2 else 1) m)) V (h+2) (S-h-2) (by omega) (by
        intro i lo hi
        obtain ⟨b,cell⟩:=suffix i (by omega) (by omega)
        have same : V i=T i:=by dsimp only [V,U,put];rw [if_neg (by omega),if_neg (by omega)]
        rw [same,cell];exact row171 k _ (modeBound _ _) b)
    rw [show h+2+(S-h-2)=S by omega] at returnPath
    have last:=keep (M:=machine k) (P:=P) (nc k 171 (changeMode (if bit then 2 else 1) m))
      (nc k 172 (changeMode (if bit then 2 else 1) m)) S S V .stay fit fit (by
        have cell : V S=none:=by dsimp only [V,U,put];rw [if_neg (by omega),if_neg (by omega),endBlank]
        rw [cell];exact row171_0 k _ (modeBound _ _)) rfl
    refine ⟨changeMode (if bit then 2 else 1) m,modeBound _ _,?_,
      flagPreserved _ m hm,badPreserved _ m hm (by cases bit <;> decide) (by cases bit <;> decide),?_⟩
    · rw [if_neg atEOF];exact liftedMode m bit
    · have combined:=joinPath (joinPath (joinPath initial lifted) returnPath) last
      rw [show 1+1+(S-h-1)+1+1+1+(S-h-2)+1=2*(S-h)+3 by omega] at combined
      simpa only [if_neg atEOF,V,U] using combined
#print axioms eof
#print axioms next
end VirtualFinalClosure.GuardForward
