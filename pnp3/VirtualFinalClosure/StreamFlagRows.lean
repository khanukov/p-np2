import VirtualFinalClosure.TableFlagMeaning
import VirtualFinalClosure.FullReplayRows
import VirtualFinalClosure.OldWire
import VirtualFinalClosure.InterceptRows
namespace VirtualFinalClosure.StreamFlagRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.FullReplayRows","VirtualFinalClosure.FullReplayRows","body_high","bodyHigh",(1:Nat)),
      ("VirtualFinalClosure.FullCursorRows","VirtualFinalClosure.FullCursorRows","base_row","baseRow",(1:Nat)),
      ("VirtualFinalClosure.OldWire","VirtualFinalClosure.OldWire","old_step","wire",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","leaf_value","leafValue",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","old_terminals","oldTerminals",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leafControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","updateFlag","updateFlag",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","next","nextFlag",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","actual_update","updateEq",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual active replay row interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual active replay row interface {mod}/{key}"
private def observed (s : Fin 64) (b : Option Bool) : Option Bool:=
  if b=none then if s.val=43 then some false else if s.val=47 then some true
    else if s.val=51 then some false else none else none
private def next (f : Fin 4) (s : Fin 64) (b : Option Bool) : Fin 4:=
  match observed s b with | none=>f | some v=>nextFlag f v
private def observed_type : Fin 64 → Option Bool → Option Bool:=observed
private def next_type : Fin 4 → Fin 64 → Option Bool → Fin 4:=next
private theorem q_value (k i : Nat) (fit : i < Cursor.stateCount k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt fit
private theorem cursor (k : Nat) (s : Fin 64) (b : Option Bool) (small : s.val < 57)
    (no39 : s.val≠39) (no40 : s.val≠40) :
    (Cursor.machine k).step (Cursor.q k s.val) b=
      (Cursor.q k (Stream.machine.step s b).1.val,(Stream.machine.step s b).2) := by
  have sv:=q_value k s.val (by unfold Cursor.stateCount;omega)
  have ca : Cursor.q k s.val≠(Cursor.machine k).accept:=by
    intro e;have h:=congrArg Fin.val e
    change (Cursor.q k s.val).val=(Cursor.q k 39).val at h
    rw [sv,q_value k 39 (by unfold Cursor.stateCount;omega)] at h
    omega
  have cr : Cursor.q k s.val≠(Cursor.machine k).reject:=by
    intro e;have h:=congrArg Fin.val e
    change (Cursor.q k s.val).val=(Cursor.q k 40).val at h
    rw [sv,q_value k 40 (by unfold Cursor.stateCount;omega)] at h
    omega
  have sa : s≠Stream.machine.accept:=by intro e;exact no39 (congrArg Fin.val e)
  have sr : s≠Stream.machine.reject:=by intro e;exact no40 (congrArg Fin.val e)
  rw [UniformTM.step_of_ne (Cursor.machine k) ca cr,
    UniformTM.step_of_ne Stream.machine sa sr]
  change Cursor.rows k (Cursor.q k s.val) b=(Cursor.q k (Stream.rows s b).1.val,(Stream.rows s b).2)
  rw [Cursor.prefix_rows k _ (by omega) (by omega) (by omega)]
  have ss : Stream.q (Cursor.q k s.val).val=s:=by apply Fin.ext;change _%64=s.val;rw [sv,Nat.mod_eq_of_lt s.isLt]
  rw [ss]
private theorem old_row (k : Nat) (s : Fin 64) (f : Fin 4) (b : Option Bool)
    (small : s.val < 57) (no39 : s.val≠39) (no40 : s.val≠40) :
    oldRow k (tableControl k s.val).val (8+f.val) b=
      ((tableControl k (Stream.machine.step s b).1.val).val,8+(next f s b).val,(Stream.machine.step s b).2) := by
  let O:=CertificateGuardClosure.machine k
  let q:=tableControl k s.val
  have nextBound : (Stream.machine.step s b).1.val < 64:=(Stream.machine.step s b).1.isLt
  have sq : s.val < Cursor.stateCount k:=by unfold Cursor.stateCount;omega
  have sv:=q_value k s.val sq
  have hs : (⟨q.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=q:=Fin.ext (Nat.mod_eq_of_lt q.isLt)
  have different (i : Nat) (bound : i < Cursor.stateCount k) (ne : s.val≠i) : q≠tableControl k i:=by
    intro e;have h:=congrArg Fin.val e
    change (tableControl k s.val).val=(tableControl k i).val at h
    rw [tableValue k s.val sq,tableValue k i bound] at h
    omega
  have leaves : ¬(q=leafControl k false ∨ q=leafControl k true):=by
    have neq (v : Bool) : q≠leafControl k v:=by
      intro e;have h:=congrArg Fin.val e
      change (tableControl k s.val).val=(leafControl k v).val at h
      rw [tableValue k s.val sq,leafValue] at h
      unfold Cursor.stateCount at h
      cases v <;> omega
    exact fun h=>h.elim (neq false) (neq true)
  have bd:=baseRow k (Cursor.q k s.val) b (by rw [sv];omega) (by rw [sv];omega) (by rw [sv];omega)
  rw [sv,cursor k s b small no39 no40] at bd
  dsimp only at bd
  rw [q_value k (Stream.machine.step s b).1.val (by have h : (Stream.machine.step s b).1.val<64:=(Stream.machine.step s b).1.isLt;unfold Cursor.stateCount;omega)] at bd
  dsimp only [oldRow]
  rw [hs,if_neg leaves]
  rw [if_neg (by intro h;rcases h.2.2 with h|h;exact different 250 (by unfold Cursor.stateCount;omega) (by omega) h;exact different 304 (by unfold Cursor.stateCount;omega) (by omega) h)]
  rw [if_neg (fun h=>different (798+93*k) (by unfold Cursor.stateCount;omega) (by omega) h.2.2)]
  rw [if_neg (fun h=>different (430+93*k) (by unfold Cursor.stateCount;omega) (by omega) h.2)]
  rw [if_neg (fun h=>different (613+93*k) (by unfold Cursor.stateCount;omega) (by omega) h.2.2)]
  rw [bd]
  dsimp only
  have noBody : ¬∃ j : Fin 3,tableControl k (Stream.machine.step s b).1.val=bodyControl k j:=by
    rintro ⟨j,e⟩;have h:=congrArg Fin.val e
    rw [tableValue k (Stream.machine.step s b).1.val (by have bb : (Stream.machine.step s b).1.val<64:=(Stream.machine.step s b).1.isLt;unfold Cursor.stateCount;omega)] at h
    have high:=bodyHigh k j
    have lim:=(Stream.machine.step s b).1.isLt
    unfold Cursor.stateCount at high
    omega
  rw [if_neg noBody]
  have eqv (i : Nat) (fit : i < Cursor.stateCount k) : q=tableControl k i ↔ s.val=i:=by
    constructor
    · intro e;have h:=congrArg Fin.val e
      change (tableControl k s.val).val=(tableControl k i).val at h
      rw [tableValue k s.val sq,tableValue k i fit] at h;omega
    · intro h;dsimp only [q];rw [h]
  simp only [eqv 43 (by unfold Cursor.stateCount;omega),eqv 47 (by unfold Cursor.stateCount;omega),eqv 51 (by unfold Cursor.stateCount;omega)]
  by_cases blank : b=none
  · simp only [blank,true_and,next,observed,ite_true]
    split_ifs <;> simp only [updateEq]
  · simp only [blank,false_and,ite_false,next,observed]
/-- Literal active product row, including the sole three observation controls.
The same tape symbol and direction are executed; nextFlag is an actual finite
state update, not an observation oracle supplied to the raw theorem. -/
private theorem effective (k : Nat) (s : Fin 64) (f : Fin 4) (b : Option Bool)
    (small : s.val < 57) (no39 : s.val≠39) (no40 : s.val≠40)
    (next39 : (Stream.machine.step s b).1.val≠39) (next40 : (Stream.machine.step s b).1.val≠40) :
    (machine k).step (control k (tableControl k s.val) ⟨8+f.val,by have h:=f.isLt;omega⟩) b=
      (control k (tableControl k (Stream.machine.step s b).1.val)
        ⟨8+(next f s b).val,by have h:=(next f s b).isLt;omega⟩,(Stream.machine.step s b).2) := by
  have nextBound : (Stream.machine.step s b).1.val < 64:=(Stream.machine.step s b).1.isLt
  have sq : s.val < Cursor.stateCount k:=by unfold Cursor.stateCount;omega
  have na : tableControl k s.val≠(CertificateGuardClosure.machine k).accept:=by
    intro e;have h:=congrArg Fin.val e
    rw [tableValue k s.val sq,(oldTerminals k).1] at h
    exact no39 (by omega)
  have nr : tableControl k s.val≠(CertificateGuardClosure.machine k).reject:=by
    intro e;have h:=congrArg Fin.val e
    rw [tableValue k s.val sq,(oldTerminals k).2] at h
    exact no40 (by omega)
  rw [wire k _ (8+f.val) b (by have h:=f.isLt;omega) na nr,old_row k s f b small no39 no40]
  dsimp only
  rw [if_neg (by
    rw [tableValue k (Stream.machine.step s b).1.val (by have h : (Stream.machine.step s b).1.val<64:=(Stream.machine.step s b).1.isLt;unfold Cursor.stateCount;omega),(oldTerminals k).1,(oldTerminals k).2]
    omega)]
  rfl
#print axioms observed_type
#print axioms next_type
#print axioms q_value
#print axioms cursor
#print axioms old_row
#print axioms effective
end VirtualFinalClosure.StreamFlagRows
