import BodyIngress.Transport
namespace BodyIngress
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier PairEncoding
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private structure Node (k : Nat) where
  state : Fin (machine k).stateCount
  head : Nat
  tape : Nat   →   Option Bool
private def put (T : Nat   →   Option Bool) (h : Nat) (b : Option Bool) : Nat   →   Option Bool :=
  fun i=>if i=h then b else T i
private def embedNode {k N B : Nat} (c : Node k) (h : c.head  <  tapeLength N B) : Config (machine k).stateCount N B :=
  ⟨c.state,⟨c.head,h⟩,fun i=>c.tape i.val⟩
private def dest (h : Nat) : Move   →   Nat
  | .left=>h-1 | .stay=>h | .right=>h+1
private structure Edge (k low high : Nat) (c d : Node k) : Prop where
  verdicts : c.state  ≠  (machine k).accept   ∧   c.state  ≠  (machine k).reject
  entry : ∀ mode:Fin 3,c.state  ≠  body k (SerializedBody.entry mode)
  before : low  ≤  c.head   ∧   c.head  ≤  high
  after : low  ≤  d.head   ∧   d.head  ≤  high
  row : (machine k).step c.state (c.tape c.head)=(d.state,((machine k).step c.state (c.tape c.head)).2)
  move : dest c.head ((machine k).step c.state (c.tape c.head)).2.2=d.head
  tape : d.tape=put c.tape c.head ((machine k).step c.state (c.tape c.head)).2.1
private inductive Path (k low high : Nat) : Nat   →   Node k   →   Node k   →   Prop
  | nil (c) (h:low  ≤  c.head   ∧   c.head  ≤  high) : Path k low high 0 c c
  | cons {t c d e} : Edge k low high c d   →   Path k low high t d e   →   Path k low high (t+1) c e
namespace Path
private theorem bounds {k lo hi t c d} (p:Path k lo hi t c d) :
    (lo  ≤  c.head   ∧   c.head  ≤  hi)   ∧   (lo  ≤  d.head   ∧   d.head  ≤  hi) := by
  induction p with
  | nil _ h=>exact ⟨h,h⟩
  | cons e _ ih=>exact ⟨e.before,ih.2⟩
private theorem append {k lo hi t u c d e} (p:Path k lo hi t c d) (q:Path k lo hi u d e) :
    Path k lo hi (t+u) c e := by
  induction p with
  | nil=>simpa using q
  | cons e _ ih=>simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons e (ih q)
private theorem step {k N B lo hi c d} (e:Edge k lo hi c d) (fit:hi  <  tapeLength N B) :
    (machine k).stepConfig (embedNode c (lt_of_le_of_lt e.before.2 fit))=
      embedNode d (lt_of_le_of_lt e.after.2 fit) := by
  apply Config.ext_parts
  · exact congrArg Prod.fst e.row
  · apply Fin.ext
    change (moveHead _ ((machine k).step c.state (c.tape c.head)).2.2).val=d.head
    have hm:=e.move
    cases mv:((machine k).step c.state (c.tape c.head)).2.2 with
    | left=>simpa only [mv,moveHead,embedNode,dest] using hm
    | stay=>simpa only [mv,moveHead,embedNode,dest] using hm
    | right=>
      rw [mv] at hm
      simp only [dest] at hm
      have room:c.head+1  <  tapeLength N B:=by have h:=e.after.2;omega
      simp only [moveHead,embedNode,room,↓reduceDIte]
      exact hm
  · funext i
    dsimp only [UniformTM.stepConfig,embedNode]
    rw [e.tape]
    simp only [put,Fin.ext_iff]
private theorem execute {k N B lo hi t c d} (p:Path k lo hi t c d) (fit:hi  <  tapeLength N B) :
    ∀ (hc:c.head  <  tapeLength N B) (hd:d.head  <  tapeLength N B),(machine k).run t (embedNode c hc)=embedNode d hd := by
  induction p with
  | nil=>intro _ _;rw [UniformTM.run]
  | @cons t c d e edge tail ih=>
    intro hc he
    rw [show t+1=1+t by omega,UniformTM.run_add]
    rw [show (machine k).run 1 (embedNode c hc)=(machine k).stepConfig (embedNode c hc) by rw [UniformTM.run,UniformTM.run]]
    rw [step edge fit]
    exact ih _ _
private theorem prefix_bounds {k N B lo hi t c d} (p:Path k lo hi t c d) (fit:hi  <  tapeLength N B) :
    ∀ u,u  <  t   →   ∀ (hc:c.head  <  tapeLength N B),
      ((machine k).run u (embedNode c hc)).state  ≠  (machine k).accept   ∧
      ((machine k).run u (embedNode c hc)).state  ≠  (machine k).reject   ∧
      (∀ mode:Fin 3,((machine k).run u (embedNode c hc)).state  ≠  body k (SerializedBody.entry mode))   ∧
      lo  ≤  ((machine k).run u (embedNode c hc)).head.val   ∧
      ((machine k).run u (embedNode c hc)).head.val  ≤  hi := by
  induction p with
  | nil=>intro u hu;omega
  | @cons t c d e ed tail ih=>
    intro u hu hc
    cases u with
    | zero=>rw [UniformTM.run];exact ⟨ed.verdicts.1,ed.verdicts.2,ed.entry,ed.before⟩
    | succ u=>
      rw [show u+1=1+u by omega,UniformTM.run_add]
      rw [show (machine k).run 1 (embedNode c hc)=(machine k).stepConfig (embedNode c hc) by rw [UniformTM.run,UniformTM.run],step ed fit]
      exact ih u (by omega) _
end Path
private theorem put_same (T:Nat   →   Option Bool) (h:Nat) : put T h (T h)=T := by
  funext i;by_cases a:i=h <;> simp [put,a]
private theorem keep {k lo hi : Nat} (s q:Fin (machine k).stateCount) (h h':Nat) (T:Nat   →   Option Bool) (mv:Move)
    (verdicts:s  ≠  (machine k).accept   ∧   s  ≠  (machine k).reject)
    (entry:∀ m:Fin 3,s  ≠  body k (SerializedBody.entry m))
    (hb:lo  ≤  h   ∧   h  ≤  hi) (ha:lo  ≤  h'   ∧   h'  ≤  hi)
    (row:(machine k).step s (T h)=(q,T h,mv)) (move:dest h mv=h') :
    Path k lo hi 1 ⟨s,h,T⟩ ⟨q,h',T⟩ := by
  apply Path.cons (d:=⟨q,h',T⟩)
  · refine ⟨verdicts,entry,hb,ha,?_,?_,?_⟩
    · rw [row]
    · rw [row];exact move
    · rw [row];exact (put_same T h).symm
  · exact Path.nil _ ha
private theorem sweepR {k lo hi : Nat} (q:Fin (machine k).stateCount) (T:Nat   →   Option Bool) (h w:Nat)
    (low:lo  ≤  h) (fit:h+w  ≤  hi)
    (verdicts:q  ≠  (machine k).accept   ∧   q  ≠  (machine k).reject)
    (entry:∀ m:Fin 3,q  ≠  body k (SerializedBody.entry m))
    (rows:∀ i,h  ≤  i   →   i  <  h+w   →   (machine k).step q (T i)=(q,T i,.right)) :
    Path k lo hi w ⟨q,h,T⟩ ⟨q,h+w,T⟩ := by
  induction w generalizing h with
  | zero=>simpa using Path.nil ⟨q,h,T⟩ ⟨low,fit⟩
  | succ w ih=>
    have one:=keep (k:=k) (lo:=lo) (hi:=hi) q q h (h+1) T .right verdicts entry ⟨low,by omega⟩ ⟨by omega,by omega⟩ (rows h le_rfl (by omega)) rfl
    have rest:=ih (h+1) (by omega) (by omega) (by intro i hl hu;exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k lo hi : Nat} (q:Fin (machine k).stateCount) (T:Nat   →   Option Bool) (h w:Nat)
    (low:lo  ≤  h) (fit:h+w  ≤  hi)
    (verdicts:q  ≠  (machine k).accept   ∧   q  ≠  (machine k).reject)
    (entry:∀ m:Fin 3,q  ≠  body k (SerializedBody.entry m))
    (rows:∀ i,h  <  i   →   i  ≤  h+w   →   (machine k).step q (T i)=(q,T i,.left)) :
    Path k lo hi w ⟨q,h+w,T⟩ ⟨q,h,T⟩ := by
  induction w with
  | zero=>simpa using Path.nil ⟨q,h,T⟩ ⟨low,fit⟩
  | succ w ih=>
    have one:=keep (k:=k) (lo:=lo) (hi:=hi) q q (h+(w+1)) (h+w) T .left verdicts entry ⟨by omega,fit⟩ ⟨by omega,by omega⟩ (rows _ (by omega) le_rfl) (by simp [dest])
    have rest:=ih (by omega) (by intro i hl hu;exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
/-- Independent finite room for all twelve fields, not inferred from old D6. -/
theorem workspace_room (R r n:Nat) (positive:1  ≤  R) (hr:r  ≤  R) (hn:n  ≤  R) :
    SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12   <
      tapeLength R (FixedRawLengthFence.allocation R) := by
  change 3*R+2+13*r+2*n+16  <  R+16*(R+1)^2+1
  nlinarith
/-- Pricing slack for the same old actual witness plus the requested installer budget. -/
theorem clock_slack (k R t d e:Nat)
    (oldBound:t+d  ≤  8589934592*(k+1)*(R+1)^5)
    (newBound:e  ≤  1073741824*(R+1)^3) :
    t+d+e  ≤  17179869184*(k+1)*(R+1)^6 := by
  have a:(R+1)^5  ≤  (R+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have b:(R+1)^3  ≤  (R+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have oldLift:=Nat.mul_le_mul_left (8589934592*(k+1)) a
  have newLift:=Nat.mul_le_mul (show 1073741824  ≤  1073741824*(k+1) by omega) b
  nlinarith only [oldBound,newBound,oldLift,newLift,Nat.zero_le ((k+1)*(R+1)^6)]

theorem check_workspace_room (R r n:Nat) (positive:1  ≤  R) (hr:r  ≤  R) (hn:n  ≤  R) :
    SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12   <
      tapeLength R (FixedRawLengthFence.allocation R) := by
  exact workspace_room R r n positive hr hn

theorem check_clock_slack (k R t d e:Nat)
    (oldBound:t+d  ≤  8589934592*(k+1)*(R+1)^5)
    (newBound:e  ≤  1073741824*(R+1)^3) :
    t+d+e  ≤  17179869184*(k+1)*(R+1)^6 := by
  exact clock_slack k R t d e oldBound newBound
end BodyIngress
