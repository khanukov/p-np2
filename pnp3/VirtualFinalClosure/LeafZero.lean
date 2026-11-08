import VirtualFinalClosure.BodyTrap
import VirtualFinalClosure.LeafFive
namespace VirtualFinalClosure.LeafZero
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.BodyTrap","VirtualFinalClosure.BodyTrap","Region","Region",(0:Nat)),
      ("VirtualFinalClosure.BodyTrap","VirtualFinalClosure.BodyTrap","safe","prefixSafe",1),
      ("VirtualFinalClosure.BodyTrapRows","VirtualFinalClosure.BodyTrapRows","full_value","bodyValue",1),
      ("VirtualFinalClosure.BodyTrapRows","VirtualFinalClosure.BodyTrapRows","carry_large","carryLarge",1),
      ("VirtualFinalClosure.LeafComponent","VirtualFinalClosure.LeafComponent","full_value","leafValue",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","E","E",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","entry_row","entryRow",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","rows","rows",1),
      ("VirtualFinalClosure.LeafFive","VirtualFinalClosure.LeafFive","prepared","five",1),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","quotient_control","quotient",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal zero-arity first-verdict term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal zero-arity first-verdict term {mod}/{key}"
private theorem extra_outside (k : Nat) (m : Fin 144) (j : Fin 8) : ¬Region k (E k m j):=by
  have ev : (E k m j).val/144=87+(VirtualLeaf.extra k j).val:=by
    dsimp only [E]
    rw [quotient,leafValue]
  have extra : (VirtualLeaf.extra k j).val=288+Cursor.stateCount k+j.val:=rfl
  have large:=carryLarge k
  rintro (eq|eq|⟨s,md,s0,s1,eq⟩)
  · have h:=congrArg (fun q=>q.val/144) eq
    dsimp only at h
    have pin:=quotient k (CertificateGuardClosure.machine k).accept ⟨8,by decide⟩
    change (machine k).accept.val/144=414 at pin
    rw [ev,pin,extra] at h
    unfold Cursor.stateCount at h
    omega
  · have h:=congrArg (fun q=>q.val/144) eq
    dsimp only at h
    have pin:=quotient k (CertificateGuardClosure.machine k).reject ⟨8,by decide⟩
    change (machine k).reject.val/144=415 at pin
    rw [ev,pin,extra] at h
    unfold Cursor.stateCount at h
    omega
  · have h:=congrArg (fun q=>q.val/144) eq
    dsimp only at h
    rw [ev,quotient,bodyValue k s s0 s1,extra] at h
    have bound:=j.isLt
    omega
/-- Actual zero-arity five rows reach literal reject, without an earlier
verdict or BODY entry anywhere on the given raw prefix. It is decoder OOB,
not a false row-value shortcut. The whole source tape is unchanged. -/
private theorem after_prefix (k N B P L s : Nat) (m : Fin 144) (T : Nat → Option Bool)
    (c : Config (machine k).stateCount N B) (fit : L+1 ≤ P) (finite : P < tapeLength N B)
    (sep : T L=none) (last : T (L+1)=none)
    (before : ∀ u,u ≤ s → ((machine k).run u c).head.val ≤ P)
    (arrived : (machine k).run s c=⟨ready k m,⟨L+1,lt_of_le_of_lt fit finite⟩,fun i=>T i.val⟩) :
    (machine k).run (s+5) c=⟨(machine k).reject,⟨L+1,lt_of_le_of_lt fit finite⟩,fun i=>T i.val⟩ ∧
      (∀ u,u < s+5 → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k
            (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ s+5 → ((machine k).run u c).head.val ≤ P):=by
  let H:=L+1
  have a:=keep (M:=machine k) (P:=P) (ready k m) (E k m ⟨0,by decide⟩) H H T .stay fit fit
    (by rw [last];exact entryRow k m) rfl
  have b:=keep (M:=machine k) (P:=P) (E k m ⟨0,by decide⟩) (E k m ⟨1,by decide⟩) H H T .stay fit fit
    (by rw [last];exact (rows k m).1) rfl
  have d:=keep (M:=machine k) (P:=P) (E k m ⟨1,by decide⟩) (E k m ⟨2,by decide⟩) H L T .left fit (by omega)
    (by rw [last];exact (rows k m).2.1) (by dsimp only [dest,H];omega)
  have e:=keep (M:=machine k) (P:=P) (E k m ⟨2,by decide⟩) (E k m ⟨3,by decide⟩) L H T .right (by omega) fit
    (by rw [sep];exact (rows k m).2.2.2) rfl
  have four:=joinPath (joinPath (joinPath a b) d) e
  have atFour : (machine k).run (s+4) c=
      ⟨E k m ⟨3,by decide⟩,⟨L+1,lt_of_le_of_lt fit finite⟩,fun i=>T i.val⟩:=by
    rw [UniformTM.run_add,arrived]
    exact execute four finite
  have safe:=prefixSafe k c (s+4) (by rw [atFour];exact extra_outside k m _)
  have path:=five k P L 0 m T (fun j=>Fin.elim0 j) fit sep last (by intro j;exact Fin.elim0 j)
  rw [dif_neg (by omega : ¬0 < (0:Nat))] at path
  refine ⟨?_,?_,?_⟩
  · rw [UniformTM.run_add,arrived]
    exact execute path finite
  · intro u hu
    exact safe u (by omega)
  · intro u hu
    by_cases initial : u ≤ s
    · exact before u initial
    · rw [show u=s+(u-s) by omega,UniformTM.run_add,arrived]
      exact through path finite (u-s) (by omega)
#print axioms extra_outside
#print axioms after_prefix
end VirtualFinalClosure.LeafZero
