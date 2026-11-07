import VirtualFinalClosure.WeightReplay
import AllArityBitLength.Kernel
import AllArityBitLength.Rows
namespace VirtualFinalClosure.SeedReplay
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("AllArityBitLength.Rows","AllArityBitLength","lookup","lookupRow",(1:Nat)),
      ("AllArityBitLength.Rows","AllArityBitLength","codes","codes",0),
      ("AllArityBitLength.Rows","AllArityBitLength","decode_row","decodeRow",1),
      ("VirtualFinalClosure.ReplayBounds","VirtualFinalClosure.ReplayBounds","reject_stays","rejectStays",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","run_lift","runLift",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.WorkspaceReplay","VirtualFinalClosure.WorkspaceReplay","slot_value","slotValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual seed replay interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual seed replay interface {mod}/{key}"
private theorem certificate (k : Nat) : (AllArityBitLength.instructions k).all
    (fun code=>decide (308 ≤ code/9 ∧ code/9 ≤ 798+93*k))=true := by
  dsimp only [AllArityBitLength.instructions]
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true,decide_eq_true_eq,and_true]
  repeat' apply And.intro
  all_goals omega
private theorem q_value (k i : Nat) (hi : i ≤ 798+93*k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
private theorem select_code (xs : List Nat) (ix : Nat) (fit : ix < xs.length) :
    let code:=xs[ix]!
    code ∈ xs ∧ xs[ix]?=some code := by
  dsimp only
  rw [getElem!_pos xs ix fit]
  exact ⟨List.getElem_mem fit,List.getElem?_eq_getElem fit⟩
private theorem row_floor (k : Nat) (q : Fin (Cursor.machine k).stateCount) (b : Option Bool)
    (lo : 308 ≤ q.val) (hi : q.val < 329) : 308 ≤ ((Cursor.machine k).step q b).1.val := by
  let sym:=match b with | none=>0 | some false=>1 | some true=>2
  have hs : sym < 3:=by cases b with | none=>decide | some v=>cases v <;> decide
  let ix:=3*(q.val-308)+sym
  have len : (AllArityBitLength.instructions k).length=63:=by rfl
  have fits : ix < (AllArityBitLength.instructions k).length:=by rw [len];dsimp only [ix];omega
  let code:=(AllArityBitLength.instructions k)[ix]!
  obtain ⟨member,atCode⟩:=select_code (AllArityBitLength.instructions k) ix fits
  have bounds:=of_decide_eq_true ((List.all_eq_true.mp (certificate k)) code member)
  have got : (codes k)[3*(q.val-64)+sym]?=some code:=by
    rw [show 3*(q.val-64)+sym=732+ix by dsimp only [ix];omega,lookupRow k ix (by rw [len] at fits;exact fits)]
    exact atCode
  have row:=decodeRow k q.val code b (by omega) hi (by omega) (by omega) (by omega) got
  have eq : Cursor.q k q.val=q:=Fin.ext (Nat.mod_eq_of_lt q.isLt)
  rw [eq] at row
  rw [row]
  change 308 ≤ (Cursor.q k (code/9)).val
  rw [q_value k (code/9) bounds.2]
  exact bounds.1
private theorem floor (k N B t : Nat) (c : Config (Cursor.machine k).stateCount N B)
    (start : c.state.val=308) (before : ∀ u,u < t → ((Cursor.machine k).run u c).state.val < 329) :
    ∀ u,u ≤ t → 308 ≤ ((Cursor.machine k).run u c).state.val := by
  intro u
  induction u with
  | zero=>intro _;change 308 ≤ c.state.val;omega
  | succ u ih=>
    intro hu
    exact row_floor k ((Cursor.machine k).run u c).state
      (((Cursor.machine k).run u c).tape ((Cursor.machine k).run u c).head) (ih (by omega)) (before u (by omega))
/-- Existing actual seed rows, on the SAME candidate, including n0/empty bank1.
No source or assignment byte is changed; the one bank3 mark is a literal write. -/
private theorem prepared (k N B L n Q F C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (positive : 0 < C) (room : L+n+1+Q < F) (sep : T L=none)
    (assn : ∀ i,L < i → i < L+n+1 → ∃ b,T i=some b) (right : T (L+n+1)=none)
    (corridor : ∀ i,L+n+1 < i → i < F → T i=none ∨ T i=some true)
    (fence : T F=some false) (d0 : T (F+1)=none)
    (b0 : ∀ i,F+1 < i → i < F+C+2 → ∃ b,T i=some b) (d1 : T (F+C+2)=none)
    (b1 : ∀ i,F+C+2 < i → i < F+C+n+3 → ∃ b,T i=some b) (d2 : T (F+C+n+3)=none)
    (b2 : ∀ i,F+C+n+3 < i → i < F+2*C+n+4 → ∃ b,T i=some b) (d3 : T (F+2*C+n+4)=none)
    (empty : T (F+2*C+n+5)=some false) (fit : F+5*C+n+7 < tapeLength N B) :
    let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 308,⟨L,by omega⟩,fun i=>T i.val⟩
    let start : Config (machine k).stateCount N B:=⟨control k (tableControl k 308) m,⟨L,by omega⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 16*(F+5*C+n+8) ∧
      (machine k).run t start=⟨control k (tableControl k 329) m,⟨F+2*C+n+4,by omega⟩,fun i=>AllArityBitLength.Target.seedImage T F C n i.val⟩ ∧
      (∀ u,u < t → ∀ flag : Fin 144,((machine k).run u start).state≠control k (tableControl k 329) flag) ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ L+16*(F+5*C+n+8)) ∧
      (∀ u,u ≤ t → (machine k).run u start=lift k m ((Cursor.machine k).run u old)) ∧
      (∀ u,u ≤ t → ((Cursor.machine k).run u old).state.val ≤ 329) := by
  intro old start
  obtain ⟨t,price,actual,before⟩:=AllArityBitLength.seed k N B L n Q F C T positive room sep assn right corridor fence d0 b0 d1 b1 d2 b2 d3 empty fit
  have ending : ((Cursor.machine k).run t old).state.val=329:=by rw [actual];exact q_value k 329 (by omega)
  have lower:=floor k N B t old (q_value k 308 (by omega)) before
  have simulation:=runLift k m old t (by
    intro u hu
    have low:=lower u hu
    by_cases early : u < t
    · have high:=before u early
      change ((Cursor.machine k).run u old).state.val < 329 at high
      omega
    · have same : u=t:=by omega
      subst u
      exact ⟨by omega,ending.le⟩) (by
    intro u hu
    have low:=lower u hu.le
    have high:=before u hu
    change ((Cursor.machine k).run u old).state.val < 329 at high
    exact ⟨high,by omega,by omega⟩)
  have initial : start=lift k m old:=by
    apply Config.ext_parts
    · exact (congrArg (fun q=>control k (tableControl k q) m) (q_value k 308 (by omega))).symm
    · rfl
    · rfl
  have done:=simulation t le_rfl
  rw [←initial,actual] at done
  refine ⟨t,price,?_,?_,?_,?_,?_⟩
  · simpa only [lift,q_value k 329 (by omega)] using done
  · intro u hu flag equal
    have current:=simulation u hu.le
    rw [←initial] at current
    have val : ((machine k).run u start).state.val=144*(375+((Cursor.machine k).run u old).state.val)+m.val:=by rw [current];exact slotValue k ((Cursor.machine k).run u old).state m
    have target:=slotValue k (Cursor.q k 329) flag
    rw [q_value k 329 (by omega)] at target
    have same:=congrArg Fin.val equal
    rw [val,target] at same
    have high:=before u hu
    change ((Cursor.machine k).run u old).state.val < 329 at high
    have fm:=m.isLt
    omega
  · intro u hu
    rw [initial,simulation u hu]
    exact ((Cursor.machine k).run_head_le (steps:=u) old).trans (by change L+u ≤ L+16*(F+5*C+n+8);omega)
  · intro u hu
    rw [initial]
    exact simulation u hu
  · intro u hu
    by_cases early : u < t
    · exact (before u early).le
    · have same : u=t:=by omega
      rw [same]
      exact ending.le
#print axioms certificate
#print axioms q_value
#print axioms select_code
#print axioms row_floor
#print axioms floor
#print axioms prepared
end VirtualFinalClosure.SeedReplay
