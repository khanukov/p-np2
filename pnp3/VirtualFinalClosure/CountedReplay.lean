import VirtualFinalClosure.CountedRows
import VirtualFinalClosure.PostStreamPlain
import VirtualFinalClosure.ArithmeticReplay
import IngressAllocation.CountTrace
import VirtualFinalClosure.FullCursorRows
import VirtualFinalClosure.ReplayBounds
import VirtualFinalClosure.Prefix
namespace VirtualFinalClosure.CountedReplay
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.CountedRows","VirtualFinalClosure.CountedRows","row","rowRange",(1:Nat)),
      ("VirtualFinalClosure.PostStreamPlain","VirtualFinalClosure.PostStreamPlain","step_plain","plainStep",1),
      ("VirtualFinalClosure.FullCursorRows","VirtualFinalClosure.FullCursorRows","base_row","baseRow",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.ReplayBounds","VirtualFinalClosure.ReplayBounds","reject_stays","rejectStays",1),
      ("VirtualFinalClosure.Prefix","VirtualFinalClosure.Prefix","config_row","configRow",1),
      ("IngressAllocation.CountTrace","IngressAllocation","counted_heads","countedHeads",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual counted replay term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual counted replay term {mod}/{key}"
private theorem q_value (k i : Nat) (hi : i ≤ 98) : (Cursor.q k i).val=i:=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
private theorem range (k N B t : Nat) (c : Config (Cursor.machine k).stateCount N B)
    (start : c.state.val=58) (finish : ((Cursor.machine k).run t c).state.val=98)
    (first : ∀ u,u  <  t → ((Cursor.machine k).run u c).state.val≠98) :
    ∀ u,u  ≤  t → 58 ≤ ((Cursor.machine k).run u c).state.val ∧
      ((Cursor.machine k).run u c).state.val ≤ 98:=by
  have reach (u : Nat) (hu : u  ≤  t) : ((Cursor.machine k).run u c).state.val=40 ∨
      ((Cursor.machine k).run u c).state.val=58 ∨ ((Cursor.machine k).run u c).state.val=64 ∨
        68  ≤  ((Cursor.machine k).run u c).state.val ∧ ((Cursor.machine k).run u c).state.val  ≤  98:=by
    induction u with
    | zero=>right;left;exact start
    | succ u ih=>
      rcases ih (by omega) with rejected|allowed
      · have eq : ((Cursor.machine k).run u c).state=(Cursor.machine k).reject:=Fin.ext rejected
        have stuck:=rejectStays ((Cursor.machine k).run u c) eq 1
        rw [←UniformTM.run_add] at stuck
        left;exact congrArg Fin.val stuck
      · have excluded:=first u (by omega)
        have same : Cursor.q k ((Cursor.machine k).run u c).state.val=((Cursor.machine k).run u c).state:=
          Fin.ext (Nat.mod_eq_of_lt ((Cursor.machine k).run u c).state.isLt)
        have row:=rowRange k ((Cursor.machine k).run u c).state.val
          (((Cursor.machine k).run u c).tape ((Cursor.machine k).run u c).head)
          (by rcases allowed with h|h|h <;> omega)
        rw [same] at row
        change ((Cursor.machine k).step ((Cursor.machine k).run u c).state
          (((Cursor.machine k).run u c).tape ((Cursor.machine k).run u c).head)).1.val=40 ∨
          _=58 ∨ _=64 ∨ 68  ≤  _ ∧ _  ≤  98
        rcases row with h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
  intro u hu
  rcases reach u hu with rejected|good
  · have eq : ((Cursor.machine k).run u c).state=(Cursor.machine k).reject:=Fin.ext rejected
    have stuck:=rejectStays ((Cursor.machine k).run u c) eq (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at stuck
    have bad : ((Cursor.machine k).run t c).state.val=40:=congrArg Fin.val stuck
    omega
  · rcases good with h|h|h <;> omega
private theorem row (k : Nat) (s : Fin (Cursor.machine k).stateCount) (m : Fin 144) (b : Option Bool)
    (lo : 58 ≤ s.val) (hi : s.val < 98)
    (afterLo : 58 ≤ ((Cursor.machine k).step s b).1.val)
    (afterHi : ((Cursor.machine k).step s b).1.val ≤ 98) :
    (machine k).step (control k (tableControl k s.val) m) b=
      (control k (tableControl k ((Cursor.machine k).step s b).1.val) m,((Cursor.machine k).step s b).2):=by
  have base:=baseRow k s b (by omega) (by omega) (by omega)
  have incoming : 432 ≤ (tableControl k s.val).val ∧ (tableControl k s.val).val < 704:=by
    rw [tableValue k s.val s.isLt];omega
  have outgoing : 432 ≤ ((CertificateGuardClosure.machine k).step (tableControl k s.val) b).1.val ∧
      ((CertificateGuardClosure.machine k).step (tableControl k s.val) b).1.val ≤ 704:=by
    rw [base];dsimp only
    rw [tableValue k ((Cursor.machine k).step s b).1.val ((Cursor.machine k).step s b).1.isLt]
    omega
  have notSpecial (i : Nat) (large : 98 ≤  i) (fit : i < Cursor.stateCount k) : tableControl k s.val≠tableControl k i:=by
    intro eq;have h:=congrArg Fin.val eq
    rw [tableValue k s.val s.isLt,tableValue k i fit] at h
    omega
  have actual:=plainStep k (tableControl k s.val) m.val b m.isLt incoming.1 incoming.2
    (notSpecial 250 (by omega) (by unfold Cursor.stateCount;omega))
    (notSpecial 304 (by omega) (by unfold Cursor.stateCount;omega)) outgoing
  rw [base] at actual
  exact actual
/-- Literal58 physical suffix counting with the SAME completed Stream flag.
Every prefix Config keeps constant metadata; source cells are restored and the
unary r marks are physically appended. No caller supplies a counted register. -/
private theorem prepared (k N B p S z n Q F : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (pos : 0 < p) (physical : p < S) (paid : 0 < Q) (room : S+z+n+3+Q < F)
    (source : ∀ i,p  ≤  i → i  <  S → ∃ b,T i=some b) (eof : T S=none)
    (reg : ∀ i,S  <  i → i  <  S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i,S+z+2 < i → i  <  S+z+n+3 → ∃ b,T i=some b)
    (right : T (S+z+n+3)=none)
    (marks : ∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap : ∀ i,S+z+n+3+Q < i → i  <  F → T i=none) (fence : T F=some false)
    (fresh : ∀ i,F < i → i  ≤  F+(S-p)+2 → T i=none)
    (fit : F+(S-p)+2 < tapeLength N B) :
    let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 58,⟨p,by omega⟩,fun i=>T i.val⟩
    let start:=lift k m old
    let t:=2+(S-p)*(2*(F-p)+6)
    (machine k).run t start=
      ⟨control k (tableControl k 98) m,⟨S,by omega⟩,fun i=>SuffixCap.Target.image T F (S-p) i.val⟩ ∧
      (∀ u,u  ≤  t → (machine k).run u start=lift k m ((Cursor.machine k).run u old)) ∧
      (∀ u,u  ≤  t → ((machine k).run u start).head.val ≤ F+(S-p)+2):=by
  intro old start t
  obtain ⟨done,first⟩:=SuffixCap.counted k N B p S z n Q F T pos physical paid room source eof reg sep assn right marks gap fence fresh fit
  have heads:=countedHeads k N B p S z n Q F T pos physical paid room source eof reg sep assn right marks gap fence fresh fit
  have finish : ((Cursor.machine k).run t old).state.val=98:=by rw [done];exact q_value k 98 le_rfl
  have strict (u : Nat) (hu : u  <  t) : ((Cursor.machine k).run u old).state.val≠98:=by
    intro eq
    apply first u hu
    apply Fin.ext
    exact eq.trans (q_value k 98 le_rfl).symm
  have band:=range k N B t old (q_value k 58 (by omega)) finish strict
  have every (u : Nat) (hu : u  ≤  t) : (machine k).run u start=lift k m ((Cursor.machine k).run u old):=by
    induction u with
    | zero=>rfl
    | succ u ih=>
      rw [UniformTM.run,ih (by omega),UniformTM.run]
      apply configRow
      exact row k _ m _ (band u (by omega)).1 (by have h:=band u (by omega);have e:=strict u (by omega);omega)
        (band (u+1) hu).1 (band (u+1) hu).2
  refine ⟨?_,every,?_⟩
  · rw [every t le_rfl,done]
    dsimp only [lift,Cursor.rReady]
    rw [q_value k 98 le_rfl]
  · intro u hu
    rw [every u hu]
    exact heads u hu
#print axioms q_value
#print axioms range
#print axioms row
#print axioms prepared
end VirtualFinalClosure.CountedReplay
