import VirtualFinalClosure.RawLengthLift
import VirtualFinalClosure.PairPrefix
import VirtualFinalClosure.EventValues
import VirtualFinalClosure.Prefix
import VirtualFinalClosure.StateFields
namespace VirtualFinalClosure.LengthPrefix
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.PairPrefix","VirtualFinalClosure.PairPrefix","raw_entry","pairPrefix",(1:Nat)),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","low_safe","lowSafe",1),
      ("VirtualFinalClosure.OriginalRows","VirtualFinalClosure.OriginalRows","Intercept","Intercept",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","every_prefix","everyPrefix",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","lift","liftPrefix",0),
      ("IngressAllocation.Extension","IngressAllocation","extend_unique","uniqueExtension",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","guarded_old","guardedOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","total_old","totalOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","body_old","bodyOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","carry_old","carryOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","virtual_old","virtualOld",1)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong strict length raw prefix interface {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique strict length raw prefix interface {mod}/{key}"
private theorem small_le_new (k R : Nat) : FixedRawLengthFence.allocation R≤allocation k R := by
  have hn : (R+1)^2≤(R+1)^(k+12):=Nat.pow_le_pow_right (by omega) (by omega)
  have hk : 1≤(k+1)^4 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right (by omega : 0<k+1) (show 0≤4 by decide)
  change 16*(R+1)^2≤281474976710656*(k+1)^4*(R+1)^(k+12)
  exact Nat.mul_le_mul (by nlinarith) hn
private theorem small_room (R : Nat) : 12*(R+1)^2+1<tapeLength R (FixedRawLengthFence.allocation R) := by
  dsimp only [tapeLength,FixedRawLengthFence.allocation]
  nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
private theorem extend_body (k R t : Nat) (y : Bitstring R)
    (heads : ∀ u,u≤t → ((BodyIngress.machine k).run u
      (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation R) y)).head.val≤12*(R+1)^2) :
    ∀ u,u≤t → (BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k) (allocation k R) y)=
      IngressAllocation.extendConfig (small_le_new k R)
        ((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation R) y)) := by
  intro u hu
  apply uniqueExtension (small_le_new k R)
  apply FixedPairParser.run_extension
  · exact FixedPairParser.initialConfig_extension _ (small_le_new k R) y
  · intro v hv
    have bound:=heads v (by omega)
    have fit:=small_room R
    omega
private theorem low_prefix_safe (k : Nat)
    (s : Fin (AllArityCursor.machine k).stateCount) (low : s.val≤617)
    (avoid250 : s≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 250))
    (avoid304 : s≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 304))
    (b : Option Bool) :
    ¬Intercept k (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (VirtualLeaf.embed k s))))) b := by
  let q:=CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (VirtualLeaf.embed k s))))
  have value:q.val=87+s.val:=by
    dsimp only [q]
    rw [guardedOld,totalOld,bodyOld,carryOld,virtualOld]
    omega
  have noLeaf (b : Bool) : q≠leafControl k b := by
    intro hit
    have same:=congrArg Fin.val hit
    rw [value,leafValue] at same
    unfold Cursor.stateCount at same
    cases b <;> omega
  have noCap (i : Nat) (range : i=250 ∨ i=304 ∨ i=798+93*k) : q≠tableControl k i := by
    intro hit
    have same:=congrArg Fin.val hit
    have bound : i<Cursor.stateCount k := by rcases range with rfl|rfl|rfl <;> unfold Cursor.stateCount <;> omega
    rw [value,tableValue k i bound] at same
    have rawValue : s.val=(SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k i)).val := by
      change s.val=288+i%Cursor.stateCount k
      rw [Nat.mod_eq_of_lt bound]
      omega
    have raw : s=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k i):=Fin.ext rawValue
    rcases range with rfl|rfl|rfl
    · exact avoid250 raw
    · exact avoid304 raw
    · omega
  intro bad
  rcases bad with h|⟨_,h⟩
  · exact h.elim (noLeaf false) (noLeaf true)
  · exact h.elim (noCap 250 (Or.inl rfl)) (fun h=>h.elim (noCap 304 (Or.inr (Or.inl rfl))) (noCap _ (Or.inr (Or.inr rfl))))
#print axioms small_le_new
#print axioms small_room
#print axioms extend_body
#print axioms low_prefix_safe
end VirtualFinalClosure.LengthPrefix
