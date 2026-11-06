import VirtualFinalClosure.CleanupState
import VirtualFinalClosure.CleanupReplay
import VirtualFinalClosure.InertCut
import VirtualFinalClosure.FirstCutCore
namespace VirtualFinalClosure.CleanupPrepared
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualReady.Kernel","VirtualReady","Frame","Frame",2),
      ("VirtualReady.Kernel","VirtualReady","Node","GNode",2),
      ("VirtualReady.Kernel","VirtualReady","Node.mk","node",3),
      ("VirtualReady.Kernel","VirtualReady","Path","GPath",2),
      ("VirtualReady.Kernel","VirtualReady","Path.nil","nilPath",3),
      ("VirtualReady.Kernel","VirtualReady","Path.cons","consPath",3),
      ("VirtualReady.Kernel","VirtualReady","Path.bounds","bounds",1),
      ("VirtualReady.Kernel","VirtualReady","Path.execute","execute",1),
      ("VirtualReady.Kernel","VirtualReady","Edge.before","edgeBefore",1),
      ("VirtualReady.Kernel","VirtualReady","embed","embed",0),
      ("VirtualReady.Kernel","VirtualReady","cleanup_path","cleanupPath",1),
      ("VirtualReady.Kernel","VirtualReady","D","D",0),
      ("VirtualReady.Kernel","VirtualReady","stage","stage",0),
      ("VirtualReady.Kernel","VirtualReady","paint","paint",0),
      ("VirtualFinalClosure.CleanupState","VirtualFinalClosure.CleanupState","region","region",0),
      ("VirtualFinalClosure.CleanupState","VirtualFinalClosure.CleanupState","run_closed","closed",1),
      ("VirtualFinalClosure.CleanupReplay","VirtualFinalClosure.CleanupReplay","run_lift","replay",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.InertCut","VirtualFinalClosure.InertCut","first","firstInert",1),
      ("VirtualLeaf.Transport","VirtualLeaf","ready_row","readyRow",1),
      ("VirtualLeaf.Transport","VirtualLeaf","ready_index","readyIndex",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","table_value","tableValue",1),
      ("VirtualFinalClosure.FirstCutCore","VirtualFinalClosure","control_injective","controlInjective",1) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual cleanup-first execution term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual cleanup-first execution term {mod}/{key}"
private theorem q_value (k i : Nat) (fit : i < Cursor.stateCount k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt fit
private theorem initial_path {k P t : Nat} {c d : GNode k} (path : GPath k P t c d)
    (u : Nat) (hu : u ≤ t) : ∃ e,GPath k P u c e:=by
  induction path generalizing u with
  | nil c fit=>
    have zero : u=0:=by omega
    subst u
    exact ⟨c,nilPath c fit⟩
  | cons edge tail ih=>
    cases u with
    | zero=>exact ⟨_,nilPath _ (edgeBefore edge)⟩
    | succ u=>
      obtain ⟨e,pre⟩:=ih u (by omega)
      exact ⟨e,consPath edge pre⟩
private theorem through {k N B P t : Nat} {c d : GNode k}
    (path : GPath k P t c d) (fit : P < tapeLength N B) :
    ∀ u,u ≤ t → ((Cursor.machine k).run u (embed c (lt_of_le_of_lt (bounds path).1 fit))).head.val ≤ P:=by
  intro u hu
  obtain ⟨e,pre⟩:=initial_path path u hu
  rw [execute pre fit]
  exact (bounds pre).2
/-- ENTIRE real dirty-bank cleanup at its FIRST old mode2 boundary, on this
active candidate with actual phase2 rows. The old absorbing deadline is NOT
copied onto the changed reader row. Every finite head is bounded by real edges. -/
private theorem prepared (k N B P L n Q F width : Nat) (T : Nat → Option Bool)
    (m : Fin 144) (ph : phase m.val=2) (fr : Frame T L n Q F width)
    (fit : D F width n 6 ≤ P) (finite : P < tapeLength N B) :
    let h0 : F+1 < tapeLength N B:=by
      change F+5*width+n+7 ≤ P at fit
      omega
    let c : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k (798+93*k),⟨F+1,h0⟩,fun j=>T j.val⟩
    ∃ (t : Nat) (hH : L+n+1 < tapeLength N B),t ≤ F-(L+n+1)+18*width+6*n+44 ∧
      (machine k).run t (lift k m c)=
        ⟨control k (tableControl k (936+93*k)) m,⟨L+n+1,hH⟩,
          fun j=>paint (stage T F width n 6) (L+1) (L+n+1) j.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u (lift k m c)).head.val ≤ P) ∧
      (∀ u,u < t → ∀ mm : Fin 144,((machine k).run u (lift k m c)).state≠control k (tableControl k (936+93*k)) mm):=by
  intro h0 c
  have path:=cleanupPath k P L n Q F width T fr fit
  have endBound : L+n+1 ≤ P := (bounds path).2
  have endFit : L+n+1 < tapeLength N B := endBound.trans_lt finite
  have oldDone:=execute (N:=N) (B:=B) path finite
  have targetQ : Cursor.q k (889+93*k+47)=Cursor.q k (936+93*k):=
    congrArg (Cursor.q k) (by omega)
  change (Cursor.machine k).run (F-(L+n+1)+18*width+6*n+44) c=
    ⟨Cursor.q k (889+93*k+47),⟨L+n+1,endFit⟩,fun j=>paint (stage T F width n 6) (L+1) (L+n+1) j.val⟩ at oldDone
  have endpointEq : (⟨Cursor.q k (889+93*k+47),⟨L+n+1,endFit⟩,fun j=>paint (stage T F width n 6) (L+1) (L+n+1) j.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.q k (936+93*k),⟨L+n+1,endFit⟩,fun j=>paint (stage T F width n 6) (L+1) (L+n+1) j.val⟩ := by
    apply Config.ext_parts
    · exact targetQ
    · rfl
    · rfl
  have oldDone := oldDone.trans endpointEq
  have oldHead:=through (N:=N) (B:=B) path finite
  have doneState : ((Cursor.machine k).run (F-(L+n+1)+18*width+6*n+44) c).state=Cursor.q k (936+93*k):=
    congrArg Config.state oldDone
  have readyRows (b : Option Bool) : (Cursor.machine k).step (Cursor.q k (936+93*k)) b=(Cursor.q k (936+93*k),b,.stay):=by
    rw [←readyIndex];exact readyRow k b
  obtain ⟨t,tp,equal,before⟩:=firstInert (Cursor.machine k) (Cursor.q k (936+93*k)) readyRows c _ doneState
  have atFirst : ((Cursor.machine k).run t c).state=Cursor.q k (936+93*k):=by rw [equal];exact doneState
  have noTerms : ((Cursor.machine k).run t c).state≠(Cursor.machine k).accept ∧
      ((Cursor.machine k).run t c).state≠(Cursor.machine k).reject:=by
    rw [atFirst]
    constructor <;> intro eq <;> have same:=congrArg Fin.val eq
    · change (Cursor.q k (936+93*k)).val=(Cursor.q k 39).val at same
      rw [q_value k _ (by unfold Cursor.stateCount;omega),q_value k _ (by unfold Cursor.stateCount;omega)] at same
      omega
    · change (Cursor.q k (936+93*k)).val=(Cursor.q k 40).val at same
      rw [q_value k _ (by unfold Cursor.stateCount;omega),q_value k _ (by unfold Cursor.stateCount;omega)] at same
      omega
  have startRegion : region k c.state:=Or.inl (q_value k _ (by unfold Cursor.stateCount;omega))
  have floor (u : Nat) (hu : u ≤ t) : 798+93*k ≤ ((Cursor.machine k).run u c).state.val:=by
    have atRegion:=closed k c startRegion u
    have notRejected:=((Cursor.machine k).no_terminal_of_le c noTerms.1 noTerms.2 u hu).2
    rcases atRegion with start|middle|ready|rejected
    · omega
    · omega
    · omega
    · exact (notRejected rejected).elim
  have beforeVal (u : Nat) (hu : u < t) : ((Cursor.machine k).run u c).state.val≠936+93*k:=by
    intro eq
    exact before u hu (Fin.ext (by rw [q_value k _ (by unfold Cursor.stateCount;omega)];exact eq))
  have actual:=replay k m c t ph floor beforeVal
  have endWhole := equal.trans oldDone
  refine ⟨t,endFit,tp,?_,?_,?_⟩
  · rw [actual t le_rfl,endWhole]
    dsimp only [lift]
    rw [q_value k _ (by unfold Cursor.stateCount;omega)]
  · intro u hu
    rw [actual u hu]
    exact oldHead u (hu.trans tp)
  · intro u hu mm impossible
    rw [actual u hu.le] at impossible
    have controls:=controlInjective k _ _ m mm impossible
    have vals:=congrArg Fin.val controls
    rw [tableValue k _ ((Cursor.machine k).run u c).state.isLt,tableValue k _ (by unfold Cursor.stateCount;omega)] at vals
    exact beforeVal u hu (by omega)
#print axioms q_value
#print axioms initial_path
#print axioms through
#print axioms prepared
end VirtualFinalClosure.CleanupPrepared
