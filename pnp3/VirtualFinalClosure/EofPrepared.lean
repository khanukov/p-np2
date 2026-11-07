import VirtualFinalClosure.EofRows
import VirtualFinalClosure.PathTrace
import VirtualFinalClosure.StreamActivePaths
import VirtualFinalClosure.LeafNativeRows
import Cursor.Proof
namespace VirtualFinalClosure.EofPrepared
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.EofRows","VirtualFinalClosure.EofRows","effective","effective",(1:Nat)),
      ("Cursor.Proof","Cursor","eof_rows","oldRows",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong EOF plain-tape execution term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique EOF plain-tape execution term {mod}/{key}"
private theorem transfer (k i : Nat) (f : Fin 4) (b w : Option Bool) (mv : Move)
    (s : Fin (Cursor.machine k).stateCount) (lo : 57 ≤ i) (hi : i ≤ 67)
    (after : 57 ≤ s.val) (old : (Cursor.machine k).step (Cursor.q k i) b=(s,w,mv)) :
    (machine k).step (q k f i) b=(control k (tableControl k s.val) ⟨8+f.val,by have h:=f.isLt;omega⟩,w,mv):=by
  have iv : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
  have actual:=effective k (Cursor.q k i) ⟨8+f.val,by have h:=f.isLt;omega⟩ b
    (by rw [iv];exact lo) (by rw [iv];exact hi) (by rw [old];exact after)
  rw [iv,old] at actual
  exact actual
private theorem qvalue (k i : Nat) (fit : i < Cursor.stateCount k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt fit
private theorem rows (k : Nat) (f : Fin 4) (b : Bool) :
    (machine k).step (q k f 57) none=(q k f 65,none,.stay) ∧
    (machine k).step (q k f 65) none=(q k f 66,none,.right) ∧
    (machine k).step (q k f 66) (some false)=(q k f 66,some false,.right) ∧
    (machine k).step (q k f 66) none=(q k f 67,none,.right) ∧
    (machine k).step (q k f 67) (some b)=(q k f 67,some b,.right) ∧
    (machine k).step (q k f 67) none=(ready k ⟨8+f.val,by have h:=f.isLt;omega⟩,none,.stay):=by
  have value : (Cursor.mReady k ⟨2,by decide⟩).val=936+93*k:=by
    unfold Cursor.mReady
    rw [qvalue k _ (by unfold Cursor.stateCount;norm_num)]
    norm_num
    omega
  obtain ⟨a,c,d,e,g,h⟩:=oldRows k b
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have actual:=transfer k 57 f none none .stay _ (by decide) (by decide) (by rw [qvalue k 65 (by unfold Cursor.stateCount;omega)];decide) a
    simpa only [qvalue k 65 (by unfold Cursor.stateCount;omega)] using actual
  · have actual:=transfer k 65 f none none .right _ (by decide) (by decide) (by rw [qvalue k 66 (by unfold Cursor.stateCount;omega)];decide) c
    simpa only [qvalue k 66 (by unfold Cursor.stateCount;omega)] using actual
  · have actual:=transfer k 66 f (some false) (some false) .right _ (by decide) (by decide) (by rw [qvalue k 66 (by unfold Cursor.stateCount;omega)];decide) d
    simpa only [qvalue k 66 (by unfold Cursor.stateCount;omega)] using actual
  · have actual:=transfer k 66 f none none .right _ (by decide) (by decide) (by rw [qvalue k 67 (by unfold Cursor.stateCount;omega)];decide) e
    simpa only [qvalue k 67 (by unfold Cursor.stateCount;omega)] using actual
  · have actual:=transfer k 67 f (some b) (some b) .right _ (by decide) (by decide) (by rw [qvalue k 67 (by unfold Cursor.stateCount;omega)];decide) g
    simpa only [qvalue k 67 (by unfold Cursor.stateCount;omega)] using actual
  · have actual:=transfer k 67 f none none .stay _ (by decide) (by decide) (by rw [value];omega) h
    simpa only [value,ready] using actual
/-- Old EOF has no installed six-bank workspace. These literal native rows
cross the actual register and occupied assignment and retain the whole T. -/
private theorem prepared (k P S z n : Nat) (f : Fin 4) (T : Nat → Option Bool)
    (fit : S+z+n+3 ≤ P) (eof : T S=none) (sep : T (S+z+2)=none)
    (last : T (S+z+n+3)=none)
    (reg : ∀ i,S < i → i < S+z+2 → T i=some false)
    (assn : ∀ i,S+z+2 < i → i < S+z+n+3 → ∃ b,T i=some b) :
    GPath (M:=machine k) P (z+n+5) (node (q k f 57) S T)
      (node (ready k ⟨8+f.val,by have h:=f.isLt;omega⟩) (S+z+n+3) T):=by
  have a:=keep (M:=machine k) (P:=P) (q k f 57) (q k f 65) S S T .stay (by omega) (by omega)
    (by rw [eof];exact (rows k f false).1) rfl
  have b:=keep (M:=machine k) (P:=P) (q k f 65) (q k f 66) S (S+1) T .right (by omega) (by omega)
    (by rw [eof];exact (rows k f false).2.1) rfl
  have c:=sweepR (M:=machine k) (P:=P) (q k f 66) T (S+1) (z+1) (by omega) (by
    intro i lo hi
    rw [reg i (by omega) (by omega)]
    exact (rows k f false).2.2.1)
  rw [show S+1+(z+1)=S+z+2 by omega] at c
  have d:=keep (M:=machine k) (P:=P) (q k f 66) (q k f 67) (S+z+2) (S+z+3) T .right (by omega) (by omega)
    (by rw [sep];exact (rows k f false).2.2.2.1) rfl
  have e:=sweepR (M:=machine k) (P:=P) (q k f 67) T (S+z+3) n (by omega) (by
    intro i lo hi
    obtain ⟨b,cell⟩:=assn i (by omega) (by omega)
    rw [cell]
    exact (rows k f b).2.2.2.2.1)
  rw [show S+z+3+n=S+z+n+3 by omega] at e
  have h:=keep (M:=machine k) (P:=P) (q k f 67) (ready k ⟨8+f.val,by have h:=f.isLt;omega⟩)
    (S+z+n+3) (S+z+n+3) T .stay fit fit (by rw [last];exact (rows k f false).2.2.2.2.2) rfl
  have path:=joinPath (joinPath (joinPath (joinPath (joinPath a b) c) d) e) h
  convert path using 1; omega
#print axioms transfer
#print axioms qvalue
#print axioms rows
#print axioms prepared
end VirtualFinalClosure.EofPrepared
