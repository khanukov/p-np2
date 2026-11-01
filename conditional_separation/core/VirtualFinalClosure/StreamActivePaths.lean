import VirtualFinalClosure.StreamFlagRows
import VirtualFinalClosure.Paths
namespace VirtualFinalClosure.StreamActivePaths
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.StreamFlagRows","VirtualFinalClosure.StreamFlagRows","effective","activeRow",(1:Nat)),
      ("VirtualFinalClosure.StreamFlagRows","VirtualFinalClosure.StreamFlagRows","observed","observed",0),
      ("VirtualFinalClosure.StreamFlagRows","VirtualFinalClosure.StreamFlagRows","next","next",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","next","nextFlag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong exact active Stream path term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact active Stream path term {mod}/{key}"
private def q (k : Nat) (f : Fin 4) (i : Nat) : Fin (machine k).stateCount:=
  control k (tableControl k i) ⟨8+f.val,by have h:=f.isLt;omega⟩
private def q_type : ∀ k,Fin 4 → Nat → Fin (machine k).stateCount:=q
private theorem pure_row (k : Nat) (f : Fin 4) (i j : Nat) (b w : Option Bool) (mv : Move)
    (small : i < 57) (fit : j < 64) (ni39 : i≠39) (ni40 : i≠40) (nj39 : j≠39) (nj40 : j≠40)
    (quiet : observed (Stream.q i) b=none)
    (row : Stream.machine.step (Stream.q i) b=(Stream.q j,w,mv)) :
    (machine k).step (q k f i) b=(q k f j,w,mv):=by
  have im : (Stream.q i).val=i:=Nat.mod_eq_of_lt (by omega)
  have jm : (Stream.q j).val=j:=Nat.mod_eq_of_lt fit
  have sameNext : next f (Stream.q i) b=f:=by dsimp only [next];rw [quiet]
  have act:=activeRow k (Stream.q i) f b (by rw [im];exact small)
    (by rwa [im]) (by rwa [im]) (by rw [row];exact fun h=>nj39 (jm.symm.trans h))
    (by rw [row];exact fun h=>nj40 (jm.symm.trans h))
  rw [row] at act
  dsimp only at act
  simpa only [q,jm,sameNext,im] using act
private theorem pay_rows (k : Nat) (f : Fin 4) : ∀ mode : Fin 3,
    (machine k).step (q k f (11+8*mode.val)) none=(q k f (41+4*mode.val),none,.right) ∧
    (machine k).step (q k f (41+4*mode.val)) (some true)=(q k f (41+4*mode.val),some true,.right) ∧
    (machine k).step (q k f (41+4*mode.val)) none=(q k f (42+4*mode.val),some true,.left) ∧
    (machine k).step (q k f (42+4*mode.val)) (some true)=(q k f (42+4*mode.val),some true,.left) ∧
    (machine k).step (q k f (42+4*mode.val)) none=(q k f (43+4*mode.val),none,.stay):=by
  intro mode
  fin_cases mode
  all_goals refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply pure_row <;> decide
/-- Literal payment on the ACTUAL active table. NO flag update occurs during
any pay scan. The unique observation is the NEXT paid/read-none edge. This
prepared fragment is consumed by the complete same-counter orbit proof. -/
private theorem pay_path (k : Nat) (f : Fin 4) (U : Nat → Option Bool) (H r cap : Nat) (mode : Fin 3)
    (blank : U H=none) (marks : ∀ i,H < i → i ≤ H+r → U i=some true)
    (fresh : U (H+r+1)=none) (room : r < cap) :
    GPath (M:=machine k) (H+cap+1) (2*r+3)
      (node (q k f (11+8*mode.val)) H U)
      (node (q k f (43+4*mode.val)) H (put U (H+r+1) (some true))):=by
  have rows:=pay_rows k f mode
  have a:=keep (M:=machine k) (q k f (11+8*mode.val)) (q k f (41+4*mode.val)) H (H+1) U .right
    (P:=H+cap+1) (by omega) (by omega) (by rw [blank];exact rows.1) rfl
  have b:=sweepR (M:=machine k) (q k f (41+4*mode.val)) U (H+1) r
    (P:=H+cap+1) (by omega) (by intro i lo hi;rw [marks i (by omega) (by omega)];exact rows.2.1)
  rw [show H+1+r=H+r+1 by omega] at b
  have c:=hop (M:=machine k) (q k f (41+4*mode.val)) (q k f (42+4*mode.val)) (H+r+1) (H+r) U (some true) .left
    (P:=H+cap+1) (by omega) (by omega) (by rw [fresh];exact rows.2.2.1) (by dsimp only [dest];omega)
  let V:=put U (H+r+1) (some true)
  have d:=sweepL (M:=machine k) (q k f (42+4*mode.val)) V H r (P:=H+cap+1) (by omega) (by
    intro i lo hi
    have hv : V i=some true:=by dsimp only [V,put];rw [if_neg (by omega),marks i lo hi]
    rw [hv];exact rows.2.2.2.1)
  have e:=keep (M:=machine k) (q k f (42+4*mode.val)) (q k f (43+4*mode.val)) H H V .stay
    (P:=H+cap+1) (by omega) (by omega) (by
      have hv : V H=none:=by dsimp only [V,put];rw [if_neg (by omega),blank]
      rw [hv];exact rows.2.2.2.2) rfl
  have result:=joinPath (joinPath (joinPath (joinPath a b) c) d) e
  convert result using 1; omega
/-- Exactly one literal paid edge, preserving the saved source bit/EOF mode.
The observed Bool is selected by the ACTUAL finite mode, never a host source read. -/
private theorem paid_row (k : Nat) (f : Fin 4) (mode : Fin 3) :
    (machine k).step (q k f (43+4*mode.val)) none=
      (q k (nextFlag f (decide (mode.val=1))) (12+8*mode.val),none,.left):=by
  have im : (Stream.q (43+4*mode.val)).val=43+4*mode.val:=Nat.mod_eq_of_lt (by have h:=mode.isLt;omega)
  have jm : (Stream.q (12+8*mode.val)).val=12+8*mode.val:=Nat.mod_eq_of_lt (by have h:=mode.isLt;omega)
  have row : Stream.machine.step (Stream.q (43+4*mode.val)) none=(Stream.q (12+8*mode.val),none,.left):=by
    fin_cases mode <;> decide
  have update : next f (Stream.q (43+4*mode.val)) none=nextFlag f (decide (mode.val=1)):=by
    fin_cases mode <;> rfl
  have act:=activeRow k (Stream.q (43+4*mode.val)) f none (by rw [im];have h:=mode.isLt;omega)
    (by rw [im];have h:=mode.isLt;omega) (by rw [im];have h:=mode.isLt;omega)
    (by rw [row];have h:=mode.isLt;rw [jm];omega) (by rw [row];have h:=mode.isLt;rw [jm];omega)
  rw [row] at act
  dsimp only at act
  simpa only [q,jm,update,im] using act
#print axioms q_type
#print axioms pure_row
#print axioms pay_rows
#print axioms pay_path
#print axioms paid_row
end VirtualFinalClosure.StreamActivePaths
