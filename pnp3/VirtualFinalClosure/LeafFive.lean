import VirtualFinalClosure.LeafNativeRows
import VirtualFinalClosure.PathTrace
namespace VirtualFinalClosure.LeafFive
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","E","E",(0:Nat)),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","result","result",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","entry_row","entryRow",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","rows","rows",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","write_row","writeRow",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","reject_row","rejectRow",1),
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",2),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","append",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong canonical-five execution interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique canonical-five execution interface {mod}/{key}"
/-- Exactly five literal edges on the frozen candidate. Canonical beta0 is at
H-1; no forward scan/reversal, no ghost workspace or installed operand. -/
private theorem prepared (k P L n : Nat) (m : Fin 144) (T : Nat → Option Bool)
    (beta : Fin n → Bool) (fit : L+n+1 ≤ P) (sep : T L=none) (last : T (L+n+1)=none)
    (digits : ∀ j : Fin n,T (L+n-j.val)=some (beta j)) :
    GPath (M:=machine k) P 5 (node (ready k m) (L+n+1) T)
      (if pos : 0<n then node (result k m (beta ⟨0,pos⟩)) (L+n+1) (put T (L+n+1) (some (beta ⟨0,pos⟩)))
       else node (machine k).reject (L+n+1) T):=by
  let H:=L+n+1
  have a:=keep (M:=machine k) (ready k m) (E k m ⟨0,by decide⟩) H H T .stay
    (P:=P) fit fit (by rw [last];exact entryRow k m) rfl
  have b:=keep (M:=machine k) (E k m ⟨0,by decide⟩) (E k m ⟨1,by decide⟩) H H T .stay
    (P:=P) fit fit (by rw [last];exact (rows k m).1) rfl
  have c:=keep (M:=machine k) (E k m ⟨1,by decide⟩) (E k m ⟨2,by decide⟩) H (L+n) T .left
    (P:=P) fit (by omega) (by rw [last];exact (rows k m).2.1) (by dsimp only [dest,H];omega)
  have abc:=append (append a b) c
  by_cases pos : 0<n
  · let value:=beta ⟨0,pos⟩
    let carry : Fin 8:=⟨if value then 5 else 4,by cases value <;> decide⟩
    have atP : T (L+n)=some value:=by simpa only [Nat.sub_zero] using digits ⟨0,pos⟩
    have d:=keep (M:=machine k) (E k m ⟨2,by decide⟩) (E k m carry) (L+n) H T .right
      (P:=P) (by omega) fit (by rw [atP];exact (rows k m).2.2.1 value) (by dsimp only [dest,H])
    have e:=hop (M:=machine k) (E k m carry) (result k m value) H H T (some value) .stay
      (P:=P) fit fit (by rw [last];exact writeRow k m value) rfl
    simpa only [dif_pos pos,value,H] using append (append abc d) e
  · have zero : n=0:=by omega
    have atP : T (L+n)=none:=by rw [zero,Nat.add_zero];exact sep
    have d:=keep (M:=machine k) (E k m ⟨2,by decide⟩) (E k m ⟨3,by decide⟩) (L+n) H T .right
      (P:=P) (by omega) fit (by rw [atP];exact (rows k m).2.2.2) (by dsimp only [dest,H])
    have e:=keep (M:=machine k) (E k m ⟨3,by decide⟩) (machine k).reject H H T .stay
      (P:=P) fit fit (by rw [last];exact rejectRow k m) rfl
    simpa only [dif_neg pos,H] using append (append abc d) e
#print axioms prepared
end VirtualFinalClosure.LeafFive
