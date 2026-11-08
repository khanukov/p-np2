import VirtualFinalClosure.StreamFlagRows
import VirtualFinalClosure.Prefix
namespace VirtualFinalClosure.QuietLow
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
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","actual_update","updateEq",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","config_row","configRow",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual active replay row interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual active replay row interface {mod}/{key}"

private theorem phase_zero (f : Fin 4) : phase (8+f.val)=0:=by fin_cases f <;> decide
private theorem row (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) (f : Fin 4) (b : Option Bool)
    (low : s.val≤375) (after : ((CertificateGuardClosure.machine k).step s b).1.val≤375) :
    (machine k).step (control k s ⟨8+f.val,by have h:=f.isLt;omega⟩) b=
      (control k ((CertificateGuardClosure.machine k).step s b).1 ⟨8+f.val,by have h:=f.isLt;omega⟩,
        ((CertificateGuardClosure.machine k).step s b).2):=by
  let O:=CertificateGuardClosure.machine k
  have hs : (⟨s.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=s:=
    Fin.ext (Nat.mod_eq_of_lt s.isLt)
  have noTable (i : Nat) (large : 43≤ i) (fit : i < Cursor.stateCount k) : s≠tableControl k i:=by
    intro e;have h:=congrArg Fin.val e
    rw [tableValue k i fit] at h
    omega
  have noLeaf (v : Bool) : s≠leafControl k v:=by
    intro e;have h:=congrArg Fin.val e
    rw [leafValue] at h
    unfold Cursor.stateCount at h
    cases v <;> omega
  have noTerm (v : Bool) : s≠(if v then O.accept else O.reject):=by
    intro e;have h:=congrArg Fin.val e
    cases v
    · rw [if_neg (by decide),(oldTerminals k).2] at h;omega
    · rw [if_pos rfl,(oldTerminals k).1] at h;omega
  rw [wire k s (8+f.val) b (by have h:=f.isLt;omega) (noTerm true) (noTerm false)]
  have original : oldRow k s.val (8+f.val) b=
      (((O.step s b).1).val,8+f.val,(O.step s b).2):=by
    dsimp only [oldRow]
    rw [hs,if_neg (fun h=>h.elim (noLeaf false) (noLeaf true))]
    rw [if_neg (by intro h;rcases h.2.2 with h|h;exact noTable 250 (by omega) (by unfold Cursor.stateCount;omega) h;exact noTable 304 (by omega) (by unfold Cursor.stateCount;omega) h)]
    rw [if_neg (fun h=>noTable (798+93*k) (by omega) (by unfold Cursor.stateCount;omega) h.2.2)]
    rw [if_neg (by intro h;have ph:=phase_zero f;omega),if_neg (by intro h;have ph:=phase_zero f;omega)]
    have nb : ¬∃ j,(O.step s b).1=bodyControl k j:=by
      rintro ⟨j,e⟩
      have h : ((CertificateGuardClosure.machine k).step s b).1.val=(bodyControl k j).val:=congrArg Fin.val e
      have hi:=bodyHigh k j
      omega
    rw [if_neg nb]
    rw [if_neg (fun h=>noTable 43 (by decide) (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noTable 47 (by decide) (by unfold Cursor.stateCount;omega) h.2),
      if_neg (fun h=>noTable 51 (by decide) (by unfold Cursor.stateCount;omega) h.2)]
  rw [original]
  dsimp only [O]
  rw [if_neg (by rw [(oldTerminals k).1,(oldTerminals k).2];omega)]
  rfl
/-- Literal parser/guard/producer prefix before the first Stream ingress keeps
its finite flag unchanged. This is whole-Config execution on the SAME tape. -/
private theorem run_prefix (k N B t : Nat) (y : Bitstring N)
    (low : ∀ u,u≤t → ((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) B y)).state.val≤375) :
    ∀ u,u≤t → (machine k).run u (initialConfig (machine k) B y)=
      config k ⟨9,by decide⟩ ((CertificateGuardClosure.machine k).run u
        (initialConfig (CertificateGuardClosure.machine k) B y)):=by
  intro u hu
  induction u with
  | zero=>rfl
  | succ u ih=>
    rw [UniformTM.run,ih (by omega),UniformTM.run]
    apply configRow
    exact row k _ ⟨1,by decide⟩ _ (low u (by omega)) (low (u+1) (by omega))
#print axioms phase_zero
#print axioms row
#print axioms run_prefix
end VirtualFinalClosure.QuietLow
