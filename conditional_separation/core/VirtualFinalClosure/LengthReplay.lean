import VirtualFinalClosure.ArithmeticReplay
import VirtualFinalClosure.WorkspaceReplay
import VirtualFinalClosure.StrictLength
import AllArityBitLength.Control
namespace VirtualFinalClosure.LengthReplay
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("AllArityBitLength.Control","AllArityBitLength","next_bound","nextBound",(1:Nat)),
      ("VirtualFinalClosure.ReplayBounds","VirtualFinalClosure.ReplayBounds","reject_stays","rejectStays",1),
      ("VirtualFinalClosure.StrictLength","VirtualFinalClosure.StrictLength","strict_phase","strictPhase",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","run_lift","runLift",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.WorkspaceReplay","VirtualFinalClosure.WorkspaceReplay","slot_value","slotValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual alternating length-replay interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual alternating length-replay interface {mod}/{key}"
private theorem q_value (k i : Nat) (hi : i ≤ 329) : (Cursor.q k i).val=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
/-- Real control closure, not an assumed lower head/control bound. Both cap
parities and the success endpoint are retained. Absorbing reject is excluded by
the ACTUAL eventual endpoint on this same run. -/
private theorem range (k N B t : Nat) (c : Config (Cursor.machine k).stateCount N B)
    (start : c.state.val=201)
    (finish : ((Cursor.machine k).run t c).state.val=250 ∨ ((Cursor.machine k).run t c).state.val=304 ∨
      ((Cursor.machine k).run t c).state.val=308)
    (first : ∀ u,u < t → ((Cursor.machine k).run u c).state.val≠250 ∧
      ((Cursor.machine k).run u c).state.val≠304 ∧ ((Cursor.machine k).run u c).state.val≠308) :
    ∀ u,u ≤ t → 201 ≤ ((Cursor.machine k).run u c).state.val ∧ ((Cursor.machine k).run u c).state.val ≤ 308 := by
  have reach : ∀ u,u ≤ t → ((Cursor.machine k).run u c).state.val=40 ∨
      (201 ≤ ((Cursor.machine k).run u c).state.val ∧ ((Cursor.machine k).run u c).state.val ≤ 308 ∧
        (((Cursor.machine k).run u c).state.val ≤ 250 ∨ 254 ≤ ((Cursor.machine k).run u c).state.val) ∧
        (((Cursor.machine k).run u c).state.val ≤ 304 ∨ 308 ≤ ((Cursor.machine k).run u c).state.val)) := by
    intro u
    induction u with
    | zero=>
      intro _
      exact Or.inr (by
        change 201 ≤ c.state.val ∧ c.state.val ≤ 308 ∧ (c.state.val ≤ 250 ∨ 254 ≤ c.state.val) ∧ (c.state.val ≤ 304 ∨ 308 ≤ c.state.val)
        omega)
    | succ u ih=>
      intro hu
      have prev:=ih (by omega)
      have excluded:=first u (by omega)
      have row:=nextBound k 201 308 (Or.inr ⟨rfl,rfl⟩) ((Cursor.machine k).run u c).state
        (((Cursor.machine k).run u c).tape ((Cursor.machine k).run u c).head)
        (by rcases prev with h|h;exact Or.inl h;exact Or.inr ⟨h.1,by omega⟩)
        (by rcases prev with h|h <;> omega)
        (by rcases prev with h|h <;> omega)
      exact row
  intro u hu
  rcases reach u hu with rejected|good
  · have rv : (Cursor.machine k).reject.val=40:=q_value k 40 (by decide)
    have equal : ((Cursor.machine k).run u c).state=(Cursor.machine k).reject:=Fin.ext (by rw [rv];exact rejected)
    have stuck:=rejectStays ((Cursor.machine k).run u c) equal (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at stuck
    have contradiction:=congrArg Fin.val stuck
    rw [rv] at contradiction
    rcases finish with h|h|h <;> omega
  · exact ⟨good.1,good.2.1⟩
/-- Full actual alternating bitLength computation on the CANDIDATE, after a
physical grown workspace, for ALL finite metadata and both actual cap parities.
Firstness is local to this q201 entry; no global raw first-q201 is asserted. -/
private theorem prepared (k N B L n Q F r : Nat) (X : Nat → Option Bool) (m : Fin 144)
    (hr : 0 < r) (paid : 0 < Q) (room : L+n+1+Q < F)
    (sep : X L=none) (assn : ∀ i,L < i → i < L+n+1 → X i=some true)
    (right : X (L+n+1)=none)
    (marks : ∀ i,L+n+1 < i → i ≤ L+n+1+Q → X i=some true)
    (gap : ∀ i,L+n+1+Q < i → i < F → X i=none)
    (fence : X F=some false) (d0 : X (F+1)=none)
    (b0 : ∀ i,F+1 < i → i < F+r+2 → X i=some true) (d1 : X (F+r+2)=none)
    (b1 : ∀ i,F+r+2 < i → i < F+r+n+3 → X i=some false) (d2 : X (F+r+n+3)=none)
    (b2 : ∀ i,F+r+n+3 < i → i < F+2*r+n+4 → X i=some false) (d3 : X (F+2*r+n+4)=none)
    (fit : F+5*r+n+7 < tapeLength N B) :
    let i:=if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304
    let h:=if bitLength n ≤ r then L else F+r+n+3
    let start : Config (machine k).stateCount N B:=⟨control k (tableControl k 201) m,⟨F+1,by omega⟩,fun j=>X j.val⟩
    ∃ (t : Nat) (hf : h < tapeLength N B),t ≤ 2048*(n+1)*(F+5*r+n+8) ∧
      (machine k).run t start=⟨control k (tableControl k i) m,⟨h,hf⟩,fun j=>RuntimeBitLength.Target.fullImage X L n F r j.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ F+5*r+n+7) ∧
      (∀ u,u < t → ∀ (j : Nat),j=250 ∨ j=304 ∨ j=308 → ∀ flag : Fin 144,
        ((machine k).run u start).state≠control k (tableControl k j) flag) ∧
      (∀ u,u ≤ t → (machine k).run u start=
        lift k m ((Cursor.machine k).run u (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun j=>X j.val⟩ : Config (Cursor.machine k).stateCount N B))) := by
  intro i h start
  let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 201,⟨F+1,by omega⟩,fun j=>X j.val⟩
  obtain ⟨t,hf,price,actual,heads,avoid,_upper⟩:=strictPhase k N B L n Q F r X hr paid room sep assn right marks gap fence d0 b0 d1 b1 d2 b2 d3 fit
  have st : old.state.val=201:=q_value k 201 (by decide)
  have ie : i=250 ∨ i=304 ∨ i=308 := by dsimp only [i];split_ifs <;> omega
  have iv : (Cursor.q k i).val=i:=q_value k i (by rcases ie with h|h|h <;> omega)
  dsimp only [i] at iv
  have endpoint : ((Cursor.machine k).run t old).state.val=i := by rw [actual];exact iv
  have ending : ((Cursor.machine k).run t old).state.val=250 ∨ ((Cursor.machine k).run t old).state.val=304 ∨ ((Cursor.machine k).run t old).state.val=308 := by rw [endpoint];exact ie
  have band:=range k N B t old st ending avoid
  have simulation:=runLift k m old t (by intro u hu;have h:=band u hu;omega) (by
    intro u hu
    have lower:=band u hu.le
    have excluded:=avoid u hu
    change ((Cursor.machine k).run u old).state.val≠250 ∧ ((Cursor.machine k).run u old).state.val≠304 ∧ ((Cursor.machine k).run u old).state.val≠308 at excluded
    exact ⟨by omega,excluded.1,excluded.2.1⟩)
  have initial : start=lift k m old := by
    apply Config.ext_parts
    · exact (congrArg (fun q=>control k (tableControl k q) m) st).symm
    · rfl
    · rfl
  have done:=simulation t le_rfl
  rw [←initial,actual] at done
  refine ⟨t,hf,price,?_,?_,?_,?_⟩
  · simpa only [lift,iv] using done
  · intro u hu
    rw [initial,simulation u hu]
    exact heads u hu
  · intro u hu j which flag equal
    have equality:=(simulation u hu.le)
    rw [←initial] at equality
    have values : ((machine k).run u start).state.val=144*(375+((Cursor.machine k).run u old).state.val)+m.val := by
      rw [equality]
      exact slotValue k ((Cursor.machine k).run u old).state m
    have target:=slotValue k (Cursor.q k j) flag
    rw [q_value k j (by rcases which with hj|hj|hj <;> omega)] at target
    have same:=congrArg Fin.val equal
    rw [values,target] at same
    have fm:=m.isLt
    have ff:=flag.isLt
    have numerical : ((Cursor.machine k).run u old).state.val=j := by omega
    have excluded:=avoid u hu
    change ((Cursor.machine k).run u old).state.val≠250 ∧ ((Cursor.machine k).run u old).state.val≠304 ∧ ((Cursor.machine k).run u old).state.val≠308 at excluded
    rcases which with hj|hj|hj <;> omega
  · intro u hu
    rw [initial]
    exact simulation u hu
#print axioms q_value
#print axioms range
#print axioms prepared
end VirtualFinalClosure.LengthReplay
