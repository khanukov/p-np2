import IngressRepair.Header
namespace IngressRepair
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private theorem prod_rows (q : Fin 288) (b : Option Bool) (good : ¬(q.val=138 ∧ b=none)) :
    producer.step q b=SmallIngress.producer.step q b := by
  simp only [UniformTM.step,producer,if_neg good]
private theorem prod_closed : ∀ (q : Fin 288) (b : Option Bool), 139≤q.val →
    139≤(SmallIngress.producer.step q b).1.val := by decide
private theorem old_closed (k : Nat) (q : Fin (machine k).stateCount) (b : Option Bool)
    (hi : 139≤q.val) : 139≤((AllArityCursor.machine k).step q b).1.val := by
  change 139≤((SmallIngress.producer.seq (Cursor.machine k)).step q b).1.val
  by_cases h : q.val<288
  · let s : Fin 288 := ⟨q.val,h⟩
    have eq : q=SmallIngress.producer.seqLeft (Cursor.machine k) s := Fin.ext rfl
    rw [eq,UniformTM.seq_step_left]
    have hs := prod_closed s b hi
    unfold UniformTM.seqRoute
    split_ifs
    · change 139≤288+0
      decide
    · change 139≤288+(Cursor.machine k).reject.val
      omega
    · exact hs
  · let s : Fin (Cursor.machine k).stateCount := ⟨q.val-288,by have lim : q.val < 288+(Cursor.machine k).stateCount := q.isLt; omega⟩
    have eq : q=SmallIngress.producer.seqRight (Cursor.machine k) s := by apply Fin.ext; change q.val=288+(q.val-288); omega
    rw [eq,UniformTM.seq_step_right]
    change 139≤288+_
    omega
private theorem raw_rows (k : Nat) (q : Fin (machine k).stateCount) (b : Option Bool)
    (good : ¬(q.val=138 ∧ b=none)) :
    (machine k).step q b=(AllArityCursor.machine k).step q b := by
  change (producer.seq (Cursor.machine k)).step q b=(SmallIngress.producer.seq (Cursor.machine k)).step q b
  by_cases h : q.val<288
  · let s : Fin 288 := ⟨q.val,h⟩
    have eq : q=producer.seqLeft (Cursor.machine k) s := Fin.ext rfl
    rw [eq,UniformTM.seq_step_left]
    have old : (SmallIngress.producer.seq (Cursor.machine k)).step (producer.seqLeft (Cursor.machine k) s) b=
      (SmallIngress.producer.seqRoute (Cursor.machine k) (SmallIngress.producer.step s b).1,
        (SmallIngress.producer.step s b).2.1,(SmallIngress.producer.step s b).2.2) :=
      UniformTM.seq_step_left SmallIngress.producer (Cursor.machine k) s b
    rw [old,prod_rows s b good]
    rfl
  · let s : Fin (Cursor.machine k).stateCount := ⟨q.val-288,by have lim : q.val < 288+(Cursor.machine k).stateCount := q.isLt; omega⟩
    have eq : q=producer.seqRight (Cursor.machine k) s := by apply Fin.ext; change q.val=288+(q.val-288); omega
    rw [eq,UniformTM.seq_step_right]
    exact (UniformTM.seq_step_right SmallIngress.producer (Cursor.machine k) s b).symm
private theorem old_run_closed (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (hi : 139≤c.state.val) (t : Nat) : 139≤((AllArityCursor.machine k).run t c).state.val := by
  induction t with
  | zero => simpa only [UniformTM.run] using hi
  | succ t ih =>
    rw [UniformTM.run]
    exact old_closed k _ _ ih
private theorem before_low (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (T : Nat) (low : ((AllArityCursor.machine k).run T c).state.val<139) :
    ∀ u, u≤T → ((AllArityCursor.machine k).run u c).state.val<139 := by
  intro u hu
  by_contra h
  have later := old_run_closed k ((AllArityCursor.machine k).run u c) (by omega) (T-u)
  rw [←UniformTM.run_add,Nat.add_sub_of_le hu] at later
  omega
private theorem prefix_equal (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (T : Nat) (safe : ∀ u, u<T → ¬(((AllArityCursor.machine k).run u c).state.val=138 ∧
      ((AllArityCursor.machine k).run u c).tape ((AllArityCursor.machine k).run u c).head=none)) :
    (machine k).run T c=(AllArityCursor.machine k).run T c := by
  induction T with
  | zero => simp only [UniformTM.run]
  | succ T ih =>
    rw [UniformTM.run,ih (by intro u hu; exact safe u (by omega)),UniformTM.run]
    have row := raw_rows k _ _ (safe T (by omega))
    simp only [UniformTM.stepConfig,row]

private theorem old_read_exit (k : Nat) (q : Fin (machine k).stateCount) (b : Option Bool)
    (atRead : q.val=138) : 139≤((AllArityCursor.machine k).step q b).1.val := by
  change 139≤((SmallIngress.producer.seq (Cursor.machine k)).step q b).1.val
  have eq : q=SmallIngress.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138) := Fin.ext atRead
  rw [eq,UniformTM.seq_step_left]
  cases b with
  | none => change 139≤140; decide
  | some b => cases b <;> first | (change 139≤143; decide) | (change 139≤139; decide)
private theorem safe_low (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (T : Nat) (low : ((AllArityCursor.machine k).run T c).state.val<139) :
    ∀ u, u<T → ¬(((AllArityCursor.machine k).run u c).state.val=138 ∧
      ((AllArityCursor.machine k).run u c).tape ((AllArityCursor.machine k).run u c).head=none) := by
  intro u hu bad
  have next := old_read_exit k _ (((AllArityCursor.machine k).run u c).tape ((AllArityCursor.machine k).run u c).head) bad.1
  have lim := before_low k c T low (u+1) (by omega)
  rw [UniformTM.run] at lim
  change 139≤((AllArityCursor.machine k).stepConfig ((AllArityCursor.machine k).run u c)).state.val at next
  omega
private theorem producer_path (k : Nat) {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (T : Nat) (safe : (SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))).state≠SmallIngress.producer.accept) :
    (AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k) B (encodePair x w))=
      SmallIngress.producer.seqEmbedRouted (Cursor.machine k)
        (SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))) := by
  change (SmallIngress.producer.seq (Cursor.machine k)).run T
    (SmallIngress.producer.seqEmbedRouted (Cursor.machine k) (initialConfig SmallIngress.producer B (encodePair x w)))=_
  refine SmallIngress.producer.seq_run_left (Cursor.machine k) _ (T := T) ?_ T le_rfl
  intro u hu bad
  have later := SmallIngress.producer.run_accept_of_le
    (initialConfig SmallIngress.producer B (encodePair x w)) bad (by omega : u≤T)
  exact safe (by rw [later]; exact bad)
private theorem raw_at_low (k : Nat) {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (T v : Nat) (hv : v<254)
    (atState : (SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))).state.val=v) :
    ((AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k) B (encodePair x w))).state.val=v := by
  have safe : (SmallIngress.producer.run T (initialConfig SmallIngress.producer B (encodePair x w))).state≠SmallIngress.producer.accept := by
    intro h; have e := congrArg Fin.val h; change _=254 at e; omega
  rw [producer_path k x w T safe]
  change (SmallIngress.producer.seqRoute (Cursor.machine k) _).val=v
  unfold UniformTM.seqRoute
  split_ifs with ha hr
  · have e := congrArg Fin.val ha; change _=254 at e; omega
  · have e := congrArg Fin.val hr; change _=255 at e; omega
  · exact atState
/-- A supported first payload cell, or width zero, preserves EVERY whole raw Config. -/
theorem supported_transport (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical : z=0 ∨ 9+z<a+m) :
    ∀ u, (machine k).run u (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      (AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) := by
  obtain ⟨T,_budget,zero,pos⟩ := header_gate x w z tag gamma
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
  have safe : ∀ u, ¬(((AllArityCursor.machine k).run u c).state.val=138 ∧
      ((AllArityCursor.machine k).run u c).tape ((AllArityCursor.machine k).run u c).head=none) := by
    by_cases hz : z=0
    · obtain ⟨a0,a1,a2⟩ := zero hz
      have r0 := raw_at_low k x w T 133 (by decide) a0
      have r1 := raw_at_low k x w (T+1) 134 (by decide) a1
      have r2 := raw_at_low k x w (T+2) 161 (by decide) a2
      intro u
      by_cases h0 : u<T
      · exact safe_low k c T (by rw [r0]; decide) u h0
      by_cases h1 : u=T
      · subst u; rw [r0]; omega
      by_cases h2 : u=T+1
      · subst u; rw [r1]; omega
      have hle : T+2≤u := by omega
      have later := old_run_closed k ((AllArityCursor.machine k).run (T+2) c) (by rw [r2]; decide) (u-(T+2))
      rw [←UniformTM.run_add,Nat.add_sub_of_le hle] at later
      omega
    · obtain ⟨h,full⟩ := pos (by omega)
      have low := raw_at_low k x w T 138 (by decide) (by rw [full]; rfl)
      have pc := producer_path k x w T (by rw [full]; change SmallIngress.q 138≠SmallIngress.producer.accept; decide)
      have read : ((AllArityCursor.machine k).run T c).tape ((AllArityCursor.machine k).run T c).head≠none := by
        rw [pc,full]
        have fit : 9+z<a+m := by rcases physical with h0 | h0; contradiction; exact h0
        simp [UniformTM.seqEmbedRouted,Function.update_apply,Fin.ext_iff,FixedRawLengthFence.fencedContentTape,fit]
        omega
      intro u
      by_cases he : u<T
      · exact safe_low k c T (by rw [low]; decide) u he
      by_cases eq : u=T
      · subst u; exact fun bad => read bad.2
      have after : 139≤((AllArityCursor.machine k).run (T+1) c).state.val := by
        rw [UniformTM.run]
        exact old_read_exit k _ _ low
      have later := old_run_closed k ((AllArityCursor.machine k).run (T+1) c) after (u-(T+1))
      rw [←UniformTM.run_add,Nat.add_sub_of_le (by omega : T+1≤u)] at later
      omega
  intro u
  exact prefix_equal k c u (fun i _ => safe i)
private theorem guard_step (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B)
    (atRead : c.state.val=138) (blank : c.tape c.head=none) :
    (machine k).stepConfig c=⟨(machine k).reject,c.head,c.tape⟩ := by
  have eq : c.state=producer.seqLeft (Cursor.machine k) (SmallIngress.q 138) := Fin.ext atRead
  have row : (machine k).step c.state (c.tape c.head)=((machine k).reject,none,.stay) := by
    rw [blank,eq]
    change (producer.seq (Cursor.machine k)).step (producer.seqLeft (Cursor.machine k) (SmallIngress.q 138)) none=_
    rw [UniformTM.seq_step_left]
    have r : producer.step (SmallIngress.q 138) none=(producer.reject,none,.stay) := by decide
    rw [r]
    rfl
  refine Config.ext_parts (congrArg Prod.fst row) ?_ ?_
  · change moveHead c.head ((machine k).step c.state (c.tape c.head)).2.2=c.head
    rw [row]; rfl
  · funext i
    change (if i=c.head then ((machine k).step c.state (c.tape c.head)).2.1 else c.tape i)=c.tape i
    rw [row]
    split_ifs with h
    · subst i; exact blank.symm
    · rfl
/-- Raw-origin literal FIRST reject when the terminator is the final physical cell.
No semantic, parsed, room or prepared-scratch premise is supplied. -/
theorem missing_payload_run (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (pos : 0<z) (short : a+m=9+z) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    let c := initialConfig (machine k) B (encodePair x w)
    ∃ (t : Nat) (h : 9+z<tapeLength (pairLength a m) B),
      t≤128*(pairLength a m+1)^2 ∧
      (machine k).run t c=⟨(machine k).reject,⟨9+z,h⟩,
        Function.update (Function.update (FixedRawLengthFence.fencedContentTape B x w)
          ⟨7,by omega⟩ none) ⟨8,by omega⟩ none⟩ ∧
      (∀ u, u<t → ((machine k).run u c).state.val<139) ∧
      (∀ u, u≤t → ((machine k).run u c).state≠(machine k).accept) := by
  obtain ⟨T,budget,_zero,read⟩ := header_gate x w z tag gamma
  obtain ⟨h,full⟩ := read pos
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let c := initialConfig (machine k) B (encodePair x w)
  have low := raw_at_low k x w T 138 (by decide) (by rw [full]; rfl)
  have whole := producer_path k x w T (by rw [full]; change SmallIngress.q 138≠SmallIngress.producer.accept; decide)
  change ((AllArityCursor.machine k).run T c).state.val=138 at low
  change (AllArityCursor.machine k).run T c=_ at whole
  have same (u : Nat) (hu : u≤T) : (machine k).run u c=(AllArityCursor.machine k).run u c :=
    prefix_equal k c u (fun v hv => safe_low k c T (by rw [low]; decide) v (by omega))
  have blank : ((AllArityCursor.machine k).run T c).tape ((AllArityCursor.machine k).run T c).head=none := by
    rw [whole,full]
    have nf : 9+z≠FixedRawLengthFence.fencePos (pairLength a m) := by simp only [FixedRawLengthFence.fencePos,pairLength]; omega
    simp [UniformTM.seqEmbedRouted,Function.update_apply,Fin.ext_iff,FixedRawLengthFence.fencedContentTape,short,nf]
  have finalStep := guard_step k ((AllArityCursor.machine k).run T c) low blank
  refine ⟨T+1,h,by omega,?_,?_,?_⟩
  · rw [UniformTM.run,same T le_rfl,finalStep,whole,full]
    rfl
  · intro u hu
    rw [same u (by omega)]
    exact before_low k c T (by rw [low]; decide) u (by omega)
  · intro u hu bad
    have later := (machine k).run_accept_of_le c bad hu
    have endReject : ((machine k).run (T+1) c).state=(machine k).reject := by
      rw [UniformTM.run,same T le_rfl,finalStep]
    rw [later,bad] at endReject
    exact (machine k).accept_ne_reject endReject
private theorem refinement (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B) (t : Nat) :
    ((machine k).run t c).state=(machine k).reject ∨
    (machine k).run t c=(AllArityCursor.machine k).run t c := by
  induction t with
  | zero => right; simp only [UniformTM.run]
  | succ t ih =>
    rcases ih with rejected | same
    · left
      have eq := (machine k).run_reject_of_le c rejected (by omega : t≤t+1)
      rw [eq]; exact rejected
    · by_cases guard : ((AllArityCursor.machine k).run t c).state.val=138 ∧
          ((AllArityCursor.machine k).run t c).tape ((AllArityCursor.machine k).run t c).head=none
      · left
        rw [UniformTM.run,same,guard_step k _ guard.1 guard.2]
      · right
        rw [UniformTM.run,same,UniformTM.run]
        have row := raw_rows k _ _ guard
        simp only [UniformTM.stepConfig,row]
/-- Every old actual literal reject remains reject at the SAME deadline.
The checked partition is unchanged whole prefix or an earlier literal guard reject. -/
theorem reject_preserved (k : Nat) {N B : Nat} (c : Config (machine k).stateCount N B) (t : Nat)
    (oldReject : ((AllArityCursor.machine k).run t c).state=(AllArityCursor.machine k).reject) :
    ((machine k).run t c).state=(machine k).reject := by
  rcases refinement k c t with rejected | same
  · exact rejected
  · rw [same]; exact oldReject

end IngressRepair
