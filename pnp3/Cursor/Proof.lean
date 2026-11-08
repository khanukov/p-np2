import Cursor.Boundary
namespace Cursor
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
private def es (k : Nat) (s : Fin Stream.machine.stateCount) : Fin (machine k).stateCount :=
  ⟨s.val,by have hs : s.val  <  64 := s.isLt; change _  <  stateCount k; unfold stateCount; omega⟩
private theorem esq (k : Nat) (i : Nat) (hi : i < 64) : es k (Stream.q i)=q k i := by
  apply Fin.ext
  simp only [es,Stream.q,q]
  rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by unfold stateCount; omega)]
private theorem body_row (k : Nat) (s : Fin Stream.machine.stateCount)
    (h57 : s.val≠57) (h58 : s.val≠58) (b : Option Bool) :
    (machine k).step (es k s) b=
      (es k (Stream.machine.step s b).1,(Stream.machine.step s b).2) := by
  by_cases ha : s=Stream.machine.accept
  · subst s
    change (machine k).step (es k (Stream.q 39)) b=_
    rw [esq k 39 (by decide)]
    change (machine k).step (machine k).accept b=_
    rw [UniformTM.step_accept,UniformTM.step_accept]
    rfl
  by_cases hr : s=Stream.machine.reject
  · subst s
    change (machine k).step (es k (Stream.q 40)) b=_
    rw [esq k 40 (by decide)]
    change (machine k).step (machine k).reject b=_
    rw [UniformTM.step_reject,UniformTM.step_reject]
    rfl
  have na : es k s≠(machine k).accept := by
    intro h; apply ha; apply Fin.ext
    have e := congrArg Fin.val h
    simpa only [es,machine,q,Nat.mod_eq_of_lt (show 39 < stateCount k by unfold stateCount; omega)] using e
  have nr : es k s≠(machine k).reject := by
    intro h; apply hr; apply Fin.ext
    have e := congrArg Fin.val h
    simpa only [es,machine,q,Nat.mod_eq_of_lt (show 40 < stateCount k by unfold stateCount; omega)] using e
  rw [UniformTM.step_of_ne _ na nr,UniformTM.step_of_ne _ ha hr]
  change rows k (es k s) b=(es k (Stream.rows s b).1,(Stream.rows s b).2)
  have sq : Stream.q s.val=s := by apply Fin.ext; exact Nat.mod_eq_of_lt s.isLt
  rw [prefix_rows k (es k s) s.isLt h57 h58 b]
  change (q k (Stream.rows (Stream.q s.val) b).1.val,(Stream.rows (Stream.q s.val) b).2)=_
  rw [sq]
  apply Prod.ext
  · apply Fin.ext
    change (Stream.rows s b).1.val % stateCount k=(Stream.rows s b).1.val
    exact Nat.mod_eq_of_lt (by have h : (Stream.rows s b).1.val < 64 := (Stream.rows s b).1.isLt; unfold stateCount; omega)
  · rfl
private def er (k : Nat) (s : Fin Stream.rawMachine.stateCount) : Fin (rawMachine k).stateCount :=
  if h : s.val < FixedRawLengthFence.prefixed.stateCount then
    FixedRawLengthFence.prefixed.seqLeft (machine k) ⟨s.val,h⟩
  else FixedRawLengthFence.prefixed.seqRight (machine k)
    (es k ⟨s.val-FixedRawLengthFence.prefixed.stateCount,by have hs : s.val  <  320 := s.isLt; change s.val-256  <  64; omega⟩)
private theorem er_left (k : Nat) (s : Fin FixedRawLengthFence.prefixed.stateCount) :
    er k (FixedRawLengthFence.prefixed.seqLeft Stream.machine s)=
      FixedRawLengthFence.prefixed.seqLeft (machine k) s := by
  simp only [er,UniformTM.seqLeft,s.isLt,↓reduceDIte]
private theorem er_right (k : Nat) (s : Fin Stream.machine.stateCount) :
    er k (FixedRawLengthFence.prefixed.seqRight Stream.machine s)=
      FixedRawLengthFence.prefixed.seqRight (machine k) (es k s) := by
  have hn : ¬FixedRawLengthFence.prefixed.stateCount+s.val < FixedRawLengthFence.prefixed.stateCount := by omega
  simp only [er,UniformTM.seqRight,hn,↓reduceDIte,Nat.add_sub_cancel_left]
private theorem er_route (k : Nat) (s : Fin FixedRawLengthFence.prefixed.stateCount) :
    er k (FixedRawLengthFence.prefixed.seqRoute Stream.machine s)=
      FixedRawLengthFence.prefixed.seqRoute (machine k) s := by
  by_cases ha : s=FixedRawLengthFence.prefixed.accept
  · simp only [UniformTM.seqRoute,ha,↓reduceIte,er_right]
    congr 1
  by_cases hr : s=FixedRawLengthFence.prefixed.reject
  · simp only [UniformTM.seqRoute,hr,↓reduceIte]
    congr 1
  simp only [UniformTM.seqRoute,ha,hr,↓reduceIte,er_left]
private def exits (s : Fin Stream.rawMachine.stateCount) : Prop := s.val=313 ∨ s.val=314
private theorem raw_row (k : Nat) (s : Fin Stream.rawMachine.stateCount)
    (he : ¬exits s) (b : Option Bool) :
    (rawMachine k).step (er k s) b=
      (er k (Stream.rawMachine.step s b).1,(Stream.rawMachine.step s b).2) := by
  change (FixedRawLengthFence.prefixed.seq (machine k)).step (er k s) b=
    (er k ((FixedRawLengthFence.prefixed.seq Stream.machine).step s b).1,
      ((FixedRawLengthFence.prefixed.seq Stream.machine).step s b).2)
  by_cases h : s.val < FixedRawLengthFence.prefixed.stateCount
  · let u : Fin FixedRawLengthFence.prefixed.stateCount := ⟨s.val,h⟩
    have eq : s=FixedRawLengthFence.prefixed.seqLeft Stream.machine u := by apply Fin.ext; rfl
    rw [eq,er_left,UniformTM.seq_step_left,UniformTM.seq_step_left,er_route]
  · let u : Fin Stream.machine.stateCount := ⟨s.val-256,by have := s.isLt; change _  <  320 at this; change ¬s.val < 256 at h; change _  < 64; omega⟩
    have eq : s=FixedRawLengthFence.prefixed.seqRight Stream.machine u := by
      apply Fin.ext; change _=256+(s.val-256); change ¬s.val < 256 at h; omega
    have h57 : u.val≠57 := by change ¬(s.val=313 ∨ s.val=314) at he; change _-256≠57; omega
    have h58 : u.val≠58 := by change ¬(s.val=313 ∨ s.val=314) at he; change _-256≠58; omega
    rw [eq,er_right,UniformTM.seq_step_right,UniformTM.seq_step_right,body_row k u h57 h58]
    rw [er_right]
private theorem old_inert {N B : Nat} (c : Config Stream.rawMachine.stateCount N B)
    (he : exits c.state) : Stream.rawMachine.stepConfig c=c := by
  rcases he with he | he
  all_goals
    have st : c.state=FixedRawLengthFence.prefixed.seqRight Stream.machine (Stream.q (if c.state.val=313 then 57 else 58)) := by
      apply Fin.ext; simp only [UniformTM.seqRight,Stream.q]; change _=256+_; simp [he]
    have row : Stream.rawMachine.step c.state (c.tape c.head)=(c.state,c.tape c.head,.stay) := by
      change (FixedRawLengthFence.prefixed.seq Stream.machine).step c.state (c.tape c.head)=_
      rw [st,UniformTM.seq_step_right]
      simp [Stream.machine,UniformTM.step,Stream.rows,Stream.q,he]
    apply Config.ext_parts
    · exact congrArg Prod.fst row
    · change moveHead c.head _=c.head; rw [row]; rfl
    · funext i; change (if i=c.head then (Stream.rawMachine.step c.state (c.tape c.head)).2.1 else c.tape i)=c.tape i
      rw [row]; split <;> rename_i h
      · subst i; rfl
      · rfl
private theorem er_val (k : Nat) (s : Fin Stream.rawMachine.stateCount) : (er k s).val=s.val := by
  unfold er
  split_ifs with h
  · rfl
  · change 256+(s.val-256)=s.val
    change ¬s.val < 256 at h
    omega
private theorem er_initial (k : Nat) {N B : Nat} (y : Bitstring N) :
    (⟨er k (initialConfig Stream.rawMachine B y).state,
      (initialConfig Stream.rawMachine B y).head,(initialConfig Stream.rawMachine B y).tape⟩ :
        Config (rawMachine k).stateCount N B)=initialConfig (rawMachine k) B y := by
  apply Config.ext_parts
  · change er k (FixedRawLengthFence.prefixed.seqRoute Stream.machine FixedRawLengthFence.prefixed.start)=
      FixedRawLengthFence.prefixed.seqRoute (machine k) FixedRawLengthFence.prefixed.start
    exact er_route k _
  · rfl
  · rfl
/-- Same literal raw input and allocation, at the FIRST old work exit.
The full head/tape is transported only before the activated rows execute. -/
theorem raw_first (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (T : Nat) (s : Fin 64) (hs : s.val=57 ∨ s.val=58)
    (h : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))))
    (U : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))) → Option Bool)
    (old : Stream.rawMachine.run T (initialConfig Stream.rawMachine
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        FixedRawLengthFence.prefixed.seqEmbedRight Stream.machine ⟨s,h,U⟩) :
    ∃ t, t ≤ T ∧ (∀ u, u < t →
      (Stream.rawMachine.run u (initialConfig Stream.rawMachine
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val≠313 ∧
      (Stream.rawMachine.run u (initialConfig Stream.rawMachine
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val≠314) ∧
      (∀ u, u < t →
        ((rawMachine k).run u (initialConfig (rawMachine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val≠313 ∧
        ((rawMachine k).run u (initialConfig (rawMachine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val≠314) ∧
      (rawMachine k).run t (initialConfig (rawMachine k)
        (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
          FixedRawLengthFence.prefixed.seqEmbedRight (machine k) ⟨q k s.val,h,U⟩ := by
  have hit : exits (Stream.rawMachine.run T (initialConfig Stream.rawMachine
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state := by
    rw [old]; change 256+s.val=313 ∨ 256+s.val=314; omega
  obtain ⟨t,ht,first,_,path,prefixPath⟩ := Transport.first_changed_rows Stream.rawMachine (rawMachine k)
    (er k) exits (fun c h => old_inert c h) (raw_row k) _ T hit
  refine ⟨t,ht,?_,?_,?_⟩
  · intro u hu; have h := first u hu; change ¬(_=313 ∨ _=314) at h; exact ⟨by tauto,by tauto⟩
  · intro u hu
    have pathu := prefixPath u (by omega)
    rw [er_initial] at pathu
    have values := congrArg (fun c => c.state.val) pathu
    dsimp only at values
    rw [er_val] at values
    have h := first u hu
    change ¬(_=313 ∨ _=314) at h
    rw [values]
    exact ⟨by tauto,by tauto⟩
  · rw [er_initial,old] at path
    have eqs : es k s=q k s.val := by
      apply Fin.ext
      change s.val=s.val % stateCount k
      symm
      have hs : s.val < 64 := s.isLt
      exact Nat.mod_eq_of_lt (by unfold stateCount; omega)
    simpa only [UniformTM.seqEmbedRight,er_right,eqs] using path

private theorem eof_rows (k : Nat) (b : Bool) :
    (machine k).step (q k 57) none=(q k 65,none,.stay) ∧
    (machine k).step (q k 65) none=(q k 66,none,.right) ∧
    (machine k).step (q k 66) (some false)=(q k 66,some false,.right) ∧
    (machine k).step (q k 66) none=(q k 67,none,.right) ∧
    (machine k).step (q k 67) (some b)=(q k 67,some b,.right) ∧
    (machine k).step (q k 67) none=(mReady k ⟨2,by decide⟩,none,.stay) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
private theorem keepR (A : UniformTM) {N B : Nat} (s d : Fin A.stateCount)
    (T : Fin (tapeLength N B) → Option Bool) (h : Nat)
    (hh : h < tapeLength N B) (hd : h+1 < tapeLength N B)
    (row : A.step s (T ⟨h,hh⟩)=(d,T ⟨h,hh⟩,.right)) :
    A.stepConfig ⟨s,⟨h,hh⟩,T⟩=⟨d,⟨h+1,hd⟩,T⟩ := by
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · change moveHead ⟨h,hh⟩ _=⟨h+1,hd⟩; rw [row]; simp [moveHead,hd]
  · funext i
    change (if i=⟨h,hh⟩ then (A.step s (T ⟨h,hh⟩)).2.1 else T i)=T i
    rw [row]; split <;> rename_i e
    · subst i; rfl
    · rfl
private theorem keepS (A : UniformTM) {N B : Nat} (s d : Fin A.stateCount)
    (T : Fin (tapeLength N B) → Option Bool) (h : Fin (tapeLength N B))
    (row : A.step s (T h)=(d,T h,.stay)) :
    A.stepConfig ⟨s,h,T⟩=⟨d,h,T⟩ := by
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · change moveHead h _=h; rw [row]; rfl
  · funext i
    change (if i=h then (A.step s (T h)).2.1 else T i)=T i
    rw [row]; split <;> rename_i e
    · subst i; rfl
    · rfl
private theorem sweepR (A : UniformTM) {N B : Nat} (s : Fin A.stateCount)
    (T : Fin (tapeLength N B) → Option Bool) (lo r : Nat) (fit : lo+r < tapeLength N B)
    (rows : ∀ i : Fin (tapeLength N B), lo ≤ i.val → i.val < lo+r → A.step s (T i)=(s,T i,.right)) :
    A.run r ⟨s,⟨lo,by omega⟩,T⟩=⟨s,⟨lo+r,fit⟩,T⟩ := by
  induction r generalizing lo with
  | zero => rfl
  | succ r ih =>
    have row := rows ⟨lo,by omega⟩ le_rfl (by change lo < lo+(r+1); omega)
    have one := keepR A s s T lo (by omega) (by omega) row
    have rest := ih (lo+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    calc
      A.run (r+1) ⟨s,⟨lo,by omega⟩,T⟩ = A.run (1+r) ⟨s,⟨lo,by omega⟩,T⟩ := by
        exact congrArg (fun u => A.run u (⟨s,⟨lo,by omega⟩,T⟩ : Config A.stateCount N B)) (by omega)
      _ = A.run r (A.stepConfig ⟨s,⟨lo,by omega⟩,T⟩) := A.run_add 1 r _
      _ = A.run r ⟨s,⟨lo+1,by omega⟩,T⟩ := congrArg (A.run r) one
      _ = ⟨s,⟨lo+(r+1),fit⟩,T⟩ := by
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
private theorem eof_kernel (k : Nat) {N B : Nat} (T : Nat → Option Bool) (S z n : Nat)
    (fit : S+z+n+3 < tapeLength N B) (hs : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (hl : T (S+z+2)=none)
    (assignment : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (hh : T (S+z+n+3)=none) :
    (machine k).run (z+n+5) ⟨q k 57,⟨S,by omega⟩,fun i => T i.val⟩=
      ⟨mReady k ⟨2,by decide⟩,⟨S+z+n+3,fit⟩,fun i => T i.val⟩ := by
  let V : Fin (tapeLength N B) → Option Bool := fun i => T i.val
  have first : (machine k).run 2 ⟨q k 57,⟨S,by omega⟩,V⟩=
      ⟨q k 66,⟨S+1,by omega⟩,V⟩ := by
    change (machine k).stepConfig ((machine k).stepConfig ⟨q k 57,⟨S,by omega⟩,V⟩)=_
    rw [keepS (machine k) (q k 57) (q k 65) V ⟨S,by omega⟩ (by simpa only [V,hs] using (eof_rows k false).1)]
    exact keepR (machine k) _ _ V S _ _ (by simpa only [V,hs] using (eof_rows k false).2.1)
  have regs := sweepR (machine k) (q k 66) V (S+1) (z+1) (by omega)
    (by intro i hlo hhi; have e := reg i.val (by omega) (by omega)
        simpa only [V,e] using (eof_rows k false).2.2.1)
  have delim := keepR (machine k) (q k 66) (q k 67) V (S+z+2) (by omega) (by omega)
    (by simpa only [V,hl] using (eof_rows k false).2.2.2.1)
  have digits := sweepR (machine k) (q k 67) V (S+z+3) n (by omega)
    (by intro i hlo hhi; obtain ⟨b,e⟩ := assignment i.val (by omega) (by omega)
        simpa only [V,e] using (eof_rows k b).2.2.2.2.1)
  have done := keepS (machine k) (q k 67) (mReady k ⟨2,by decide⟩) V ⟨S+z+n+3,fit⟩
    (by simpa only [V,hh] using (eof_rows k false).2.2.2.2.2)
  simp only [show S+1+(z+1)=S+z+2 by omega] at regs
  simp only [show S+z+3+n=S+z+n+3 by omega] at digits
  have delimRun : (machine k).run 1 ⟨q k 66,⟨S+z+2,by omega⟩,V⟩=
      ⟨q k 67,⟨S+z+3,by omega⟩,V⟩ := by
    simpa only [show S+z+2+1=S+z+3 by omega] using delim
  have doneRun : (machine k).run 1 ⟨q k 67,⟨S+z+n+3,fit⟩,V⟩=
      ⟨mReady k ⟨2,by decide⟩,⟨S+z+n+3,fit⟩,V⟩ := done
  rw [show z+n+5=2+(z+1)+1+n+1 by omega]
  rw [UniformTM.run_add,UniformTM.run_add,UniformTM.run_add,UniformTM.run_add,first,regs,delimRun,digits,doneRun]
/-- New scratch starts beyond the ACTUAL raw false fence; no clean tape premise. -/
theorem raw_tail_blank {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (room : n < FixedRawLengthFence.capacity a m z)
    (fits : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
      (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (a+m+z+2) n)
    let T := Stream.Target.image U (a+m) z n (9+2*z) (2^n) (2^n) false
    (∀ i : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      FixedRawLengthFence.fencePos (pairLength a m) < i.val → T i.val=none) ∧
    FixedRawLengthFence.fencePos (pairLength a m)+5*((a+m)-min (9+2*z+2^n) (a+m))+n+7  <
      tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) := by
  have geo := (Stream.raw_budget_cells x w gamma room).1
  refine ⟨?_,?_⟩
  · intro i hi
    dsimp only [Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    dsimp only [Body.extend]
    rw [dif_pos i.isLt]
    dsimp only [Body.installedTape]
    rw [if_neg (by omega)]
    dsimp only [FixedRawLengthFence.countdownTape]
    rw [if_neg (by omega)]
    simp only [FixedGammaTargetUnaryCountdown.loopTape]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  · have rem : (a+m)-min (9+2*z+2^n) (a+m) ≤ a+m := Nat.sub_le _ _
    dsimp only [FixedRawLengthFence.fencePos,FixedRawLengthFence.allocation,pairLength,tapeLength] at *
    nlinarith only [geo,rem,Nat.zero_le ((2*a+m+1)*(2*a+m+1))]

/-- Literal RAW to MReady for the virtual table-end branch. No content verdict. -/
theorem raw_eof (k : Nat) : Boundary.EOF k := by
  intro a m x w pr parsed tag hn
  obtain ⟨z,hz,gamma,stage⟩ := Stream.raw_body k x w parsed tag hn
  refine ⟨z,hz,gamma,?_⟩
  intro room full fits eof
  obtain ⟨T,hH,price,_,finish⟩ := stage room full
  rw [if_pos fits] at finish
  obtain ⟨hp,old⟩ := finish
  have pc : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m := Nat.min_eq_right eof
  simp only [pc,↓reduceIte] at hp old
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let n := pr.2.n
  let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 n) (S+z+2) n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  obtain ⟨t,ht,_,_,pre⟩ := raw_first k x w T (Stream.q 57) (Or.inl rfl) ⟨S,hp⟩ (fun i => V i.val) old
  rw [show (Stream.q 57).val=57 from rfl] at pre
  have geom := (Stream.raw_budget_cells x w gamma room).1
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma
    (FixedRawLengthFence.resource_bounds R).1 (Nat.le_of_lt room)
  have frame (i : Nat) (hi : i ≤ S+z+2) : V i=U i := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    rfl
  have installed (i : Nat) (hi : i ≤ S+z+2) : U i=
      FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,by dsimp [S,n,B,R] at *; omega⟩ := by
    dsimp only [U,Body.extend]
    rw [dif_pos (by dsimp [S,n,B,R] at *; omega)]
    dsimp only [Body.installedTape]
    rw [if_neg (by omega)]
  have vs : V S=none := by
    rw [frame _ (by omega),installed _ (by omega)]
    simp only [FixedRawLengthFence.countdownTape]
    rw [if_neg (by dsimp [FixedRawLengthFence.fencePos,pairLength,S,R] at *; omega)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
  have vl : V (S+z+2)=none := by
    rw [frame _ le_rfl,installed _ le_rfl]
    exact cells.2.2.1 _ (by dsimp [S]; omega)
  have vr (i : Nat) (lo : S < i) (hi : i < S+z+2) : V i=some false := by
    rw [frame _ (by omega),installed _ (by omega)]
    exact cells.2.1 (i-S-1) (by omega) _ (by dsimp [S]; omega)
  have va (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : ∃ b, V i=some b := by
    dsimp only [V,Stream.Target.image]
    rw [if_pos (by omega)]
    exact ⟨_,rfl⟩
  have vh : V (S+z+n+3)=none := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    dsimp only [U,Body.extend]
    rw [dif_pos hH]
    dsimp only [Body.installedTape]
    rw [if_neg (by omega),if_neg (by omega)]
    exact cells.2.2.2.2.1 ⟨S+z+n+3,hH⟩
      (by change a+m+3+z+n ≤ S+z+n+3; dsimp only [S]; omega) geom
  have tail := eof_kernel k V S z n hH vs vr vl va vh
  have isVirtual : S ≤ Target.M k n z := by unfold Target.M; dsimp [S,n] at *; omega
  refine ⟨t+(z+n+5),hH,?_,isVirtual,?_,?_⟩
  · have small : z+n+5 ≤ 3*R+4 := by dsimp [n,S,R,FixedRawLengthFence.fencePos] at *; omega
    have bound : t+(z+n+5) ≤ 4096*(R+1)^2 := by nlinarith only [ht,price,small,Nat.zero_le (R*R)]
    have powers : (R+1)^2 ≤ (R+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
    exact bound.trans (Nat.mul_le_mul (by omega) powers)
  · unfold padRead
    rw [dif_neg (by change ¬Target.M k n z < S; omega)]
  · rw [UniformTM.run_add,pre]
    change (FixedRawLengthFence.prefixed.seq (machine k)).run (z+n+5)
      (FixedRawLengthFence.prefixed.seqEmbedRight (machine k) ⟨q k 57,⟨S,hp⟩,fun i => V i.val⟩)=
      FixedRawLengthFence.prefixed.seqEmbedRight (machine k)
        ⟨mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩
    rw [FixedRawLengthFence.prefixed.seq_run_right,tail]
/-- Every old literal raw rejection survives activating the two work exits. -/
theorem raw_reject (k : Nat) {N B : Nat} (y : Bitstring N) (T : Nat)
    (h : Fin (tapeLength N B)) (U : Fin (tapeLength N B) → Option Bool)
    (old : Stream.rawMachine.run T (initialConfig Stream.rawMachine B y)=
      FixedRawLengthFence.prefixed.seqEmbedRight Stream.machine ⟨Stream.machine.reject,h,U⟩) :
    (rawMachine k).run T (initialConfig (rawMachine k) B y)=
      FixedRawLengthFence.prefixed.seqEmbedRight (machine k) ⟨(machine k).reject,h,U⟩ := by
  have outside : ¬exits (Stream.rawMachine.run T (initialConfig Stream.rawMachine B y)).state := by
    rw [old]
    change ¬(256+40=313 ∨ 256+40=314)
    decide
  have path := Transport.avoid_changed_rows Stream.rawMachine (rawMachine k) (er k) exits
    (fun c h => old_inert c h) (raw_row k) _ T outside
  rw [er_initial,old] at path
  simpa only [UniformTM.seqEmbedRight,er_right,
    show es k Stream.machine.reject=(machine k).reject from rfl] using path

/-- Accepted specialization discharges every physical guard in the EOF branch.
The p<S arithmetic branch is still the full RED Target.Raw obligation. -/
theorem raw_accepted_eof (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n≤a+m ∧
      (3≤pr.2.n → ∃ z, 2≤z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        (a+m≤9+2*z+2^pr.2.n →
          ∃ (t : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
            t≤Target.deadline k (pairLength a m) ∧ a+m≤Target.M k pr.2.n z ∧
            padRead (Fin.append x w) (Target.M k pr.2.n z)=false ∧
            let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
              (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
            let T := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
            (rawMachine k).run t (initialConfig (rawMachine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
              FixedRawLengthFence.prefixed.seqEmbedRight (machine k)
                ⟨mReady k ⟨2,by decide⟩,⟨a+m+z+pr.2.n+3,hH⟩,fun i => T i.val⟩)) := by
  obtain ⟨pr,parsed,table,_⟩ := AcceptedBody.exact k x w accepted
  refine ⟨pr,parsed,table,?_⟩
  intro hn
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true := by
    have h := accepted
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
    split at h
    · rename_i shape; cases shape; rwa [AcceptedBody.concat_eq_append] at h
    · contradiction
  have tag : FixedContentTagGate.tagMatches (Fin.append x w)=true := by
    have h := fixedTag_semantic_factorization.1 (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)
    rw [semantic] at h
    simpa using h.symm
  obtain ⟨z,hz,gamma,stage⟩ := raw_eof k x w parsed tag hn
  have full := GammaSupport.exact k x w parsed semantic hn z gamma
  have small : pr.2.n≤a+m := by
    have h := Nat.lt_two_pow_self (n := pr.2.n)
    change 2^pr.2.n≤a+m at table
    omega
  have room := AcceptedBody.strict_capacity x w gamma small
  have fits := Stream.accepted_rows_fit k x w accepted parsed gamma
  exact ⟨z,hz,gamma,stage room full fits⟩
end Cursor
