import AllArityCursor.Target
import SuffixCap.Rows
namespace AllArityCursor
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Cursor
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private def es (k : Nat) (s : Fin Stream.machine.stateCount) : Fin (Cursor.machine k).stateCount :=
  ⟨s.val,by have hs : s.val  <  64 := s.isLt; change _  <  stateCount k; unfold stateCount; omega⟩
private theorem esq (k : Nat) (i : Nat) (hi : i < 64) : es k (Stream.q i)=q k i := by
  apply Fin.ext
  simp only [es,Stream.q,q]
  rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by unfold stateCount; omega)]
private theorem body_row (k : Nat) (s : Fin Stream.machine.stateCount)
    (h57 : s.val≠57) (h58 : s.val≠58) (b : Option Bool) :
    (Cursor.machine k).step (es k s) b=
      (es k (Stream.machine.step s b).1,(Stream.machine.step s b).2) := by
  by_cases ha : s=Stream.machine.accept
  · subst s
    change (Cursor.machine k).step (es k (Stream.q 39)) b=_
    rw [esq k 39 (by decide)]
    change (Cursor.machine k).step (Cursor.machine k).accept b=_
    rw [UniformTM.step_accept,UniformTM.step_accept]
    rfl
  by_cases hr : s=Stream.machine.reject
  · subst s
    change (Cursor.machine k).step (es k (Stream.q 40)) b=_
    rw [esq k 40 (by decide)]
    change (Cursor.machine k).step (Cursor.machine k).reject b=_
    rw [UniformTM.step_reject,UniformTM.step_reject]
    rfl
  have na : es k s≠(Cursor.machine k).accept := by
    intro h; apply ha; apply Fin.ext
    have e := congrArg Fin.val h
    simpa only [es,Cursor.machine,q,Nat.mod_eq_of_lt (show 39 < stateCount k by unfold stateCount; omega)] using e
  have nr : es k s≠(Cursor.machine k).reject := by
    intro h; apply hr; apply Fin.ext
    have e := congrArg Fin.val h
    simpa only [es,Cursor.machine,q,Nat.mod_eq_of_lt (show 40 < stateCount k by unfold stateCount; omega)] using e
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
private def er (k : Nat) (s : Fin SmallIngress.machine.stateCount) : Fin (machine k).stateCount :=
  if h : s.val < SmallIngress.producer.stateCount then
    SmallIngress.producer.seqLeft (Cursor.machine k) ⟨s.val,h⟩
  else SmallIngress.producer.seqRight (Cursor.machine k)
    (es k ⟨s.val-SmallIngress.producer.stateCount,by have hs : s.val  <  352 := s.isLt; change s.val-288  <  64; omega⟩)
private theorem er_left (k : Nat) (s : Fin SmallIngress.producer.stateCount) :
    er k (SmallIngress.producer.seqLeft Stream.machine s)=
      SmallIngress.producer.seqLeft (Cursor.machine k) s := by
  simp only [er,UniformTM.seqLeft,s.isLt,↓reduceDIte]
private theorem er_right (k : Nat) (s : Fin Stream.machine.stateCount) :
    er k (SmallIngress.producer.seqRight Stream.machine s)=
      SmallIngress.producer.seqRight (Cursor.machine k) (es k s) := by
  have hn : ¬SmallIngress.producer.stateCount+s.val < SmallIngress.producer.stateCount := by omega
  simp only [er,UniformTM.seqRight,hn,↓reduceDIte,Nat.add_sub_cancel_left]
private theorem er_route (k : Nat) (s : Fin SmallIngress.producer.stateCount) :
    er k (SmallIngress.producer.seqRoute Stream.machine s)=
      SmallIngress.producer.seqRoute (Cursor.machine k) s := by
  by_cases ha : s=SmallIngress.producer.accept
  · simp only [UniformTM.seqRoute,ha,↓reduceIte,er_right]
    congr 1
  by_cases hr : s=SmallIngress.producer.reject
  · simp only [UniformTM.seqRoute,hr,↓reduceIte]
    congr 1
  simp only [UniformTM.seqRoute,ha,hr,↓reduceIte,er_left]
private def exits (s : Fin SmallIngress.machine.stateCount) : Prop := s.val=345 ∨ s.val=346
private theorem raw_row (k : Nat) (s : Fin SmallIngress.machine.stateCount)
    (he : ¬exits s) (b : Option Bool) :
    (machine k).step (er k s) b=
      (er k (SmallIngress.machine.step s b).1,(SmallIngress.machine.step s b).2) := by
  change (SmallIngress.producer.seq (Cursor.machine k)).step (er k s) b=
    (er k ((SmallIngress.producer.seq Stream.machine).step s b).1,
      ((SmallIngress.producer.seq Stream.machine).step s b).2)
  by_cases h : s.val < SmallIngress.producer.stateCount
  · let u : Fin SmallIngress.producer.stateCount := ⟨s.val,h⟩
    have eq : s=SmallIngress.producer.seqLeft Stream.machine u := by apply Fin.ext; rfl
    rw [eq,er_left,UniformTM.seq_step_left,UniformTM.seq_step_left,er_route]
  · let u : Fin Stream.machine.stateCount := ⟨s.val-288,by have := s.isLt; change _  <  352 at this; change ¬s.val < 288 at h; change _  < 64; omega⟩
    have eq : s=SmallIngress.producer.seqRight Stream.machine u := by
      apply Fin.ext; change _=288+(s.val-288); change ¬s.val < 288 at h; omega
    have h57 : u.val≠57 := by change ¬(s.val=345 ∨ s.val=346) at he; change _-288≠57; omega
    have h58 : u.val≠58 := by change ¬(s.val=345 ∨ s.val=346) at he; change _-288≠58; omega
    rw [eq,er_right,UniformTM.seq_step_right,UniformTM.seq_step_right,body_row k u h57 h58]
    rw [er_right]
private theorem old_inert {N B : Nat} (c : Config SmallIngress.machine.stateCount N B)
    (he : exits c.state) : SmallIngress.machine.stepConfig c=c := by
  rcases he with he | he
  all_goals
    have st : c.state=SmallIngress.producer.seqRight Stream.machine (Stream.q (if c.state.val=345 then 57 else 58)) := by
      apply Fin.ext; simp only [UniformTM.seqRight,Stream.q]; change _=288+_; simp [he]
    have row : SmallIngress.machine.step c.state (c.tape c.head)=(c.state,c.tape c.head,.stay) := by
      change (SmallIngress.producer.seq Stream.machine).step c.state (c.tape c.head)=_
      rw [st,UniformTM.seq_step_right]
      simp [Stream.machine,UniformTM.step,Stream.rows,Stream.q,he]
    apply Config.ext_parts
    · exact congrArg Prod.fst row
    · change moveHead c.head _=c.head; rw [row]; rfl
    · funext i; change (if i=c.head then (SmallIngress.machine.step c.state (c.tape c.head)).2.1 else c.tape i)=c.tape i
      rw [row]; split <;> rename_i h
      · subst i; rfl
      · rfl
private theorem er_val (k : Nat) (s : Fin SmallIngress.machine.stateCount) : (er k s).val=s.val := by
  unfold er
  split_ifs with h
  · rfl
  · change 288+(s.val-288)=s.val
    change ¬s.val < 288 at h
    omega
private theorem er_initial (k : Nat) {N B : Nat} (y : Bitstring N) :
    (⟨er k (initialConfig SmallIngress.machine B y).state,
      (initialConfig SmallIngress.machine B y).head,(initialConfig SmallIngress.machine B y).tape⟩ :
        Config (machine k).stateCount N B)=initialConfig (machine k) B y := by
  apply Config.ext_parts
  · change er k (SmallIngress.producer.seqRoute Stream.machine SmallIngress.producer.start)=
      SmallIngress.producer.seqRoute (Cursor.machine k) SmallIngress.producer.start
    exact er_route k _
  · rfl
  · rfl

private theorem es_val_q (k : Nat) (s : Fin Stream.machine.stateCount) :
    es k s=Cursor.q k s.val := by
  apply Fin.ext
  change s.val=s.val % Cursor.stateCount k
  symm
  exact Nat.mod_eq_of_lt (by have h : s.val < 64 := s.isLt; unfold Cursor.stateCount; omega)
private theorem map_er (k : Nat) {N B : Nat} (c : Config SmallIngress.machine.stateCount N B) :
    (⟨er k c.state,c.head,c.tape⟩ : Config (machine k).stateCount N B)=mapOld k c := by
  apply Config.ext_parts
  · apply Fin.ext; exact er_val k c.state
  · rfl
  · rfl
private theorem map_initial (k : Nat) {N B : Nat} (v : Bitstring N) :
    mapOld k (initialConfig SmallIngress.machine B v)=initialConfig (machine k) B v :=
  (map_er k _).symm.trans (er_initial k v)
private theorem map_right (k : Nat) {N B : Nat} (c : Config Stream.machine.stateCount N B) :
    mapOld k (SmallIngress.producer.seqEmbedRight Stream.machine c)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k c.state.val,c.head,c.tape⟩ := by
  rw [←map_er]
  simp only [UniformTM.seqEmbedRight,er_right,es_val_q]
private theorem first_raw (k : Nat) {N B : Nat} (v : Bitstring N)
    (T : Nat) (s : Fin 64) (hs : s.val=57 ∨ s.val=58)
    (h : Fin (tapeLength N B)) (V : Fin (tapeLength N B) → Option Bool)
    (old : SmallIngress.machine.run T (initialConfig SmallIngress.machine B v)=
      SmallIngress.producer.seqEmbedRight Stream.machine ⟨s,h,V⟩) :
    ∃ t, t ≤ T ∧
      SmallIngress.machine.run t (initialConfig SmallIngress.machine B v)=
        SmallIngress.producer.seqEmbedRight Stream.machine ⟨s,h,V⟩ ∧
      (∀ u, u ≤ t → (machine k).run u (initialConfig (machine k) B v)=
        mapOld k (SmallIngress.machine.run u (initialConfig SmallIngress.machine B v))) ∧
      (∀ u, u < t →
        (SmallIngress.machine.run u (initialConfig SmallIngress.machine B v)).state.val≠345 ∧
        (SmallIngress.machine.run u (initialConfig SmallIngress.machine B v)).state.val≠346 ∧
        ((machine k).run u (initialConfig (machine k) B v)).state.val≠345 ∧
        ((machine k).run u (initialConfig (machine k) B v)).state.val≠346) := by
  have hit : exits (SmallIngress.machine.run T (initialConfig SmallIngress.machine B v)).state := by
    rw [old]; change 288+s.val=345 ∨ 288+s.val=346; omega
  obtain ⟨t,ht,first,same,_last,prefixPath⟩ := Transport.first_changed_rows
    SmallIngress.machine (machine k) (er k) exits (fun c hc => old_inert c hc) (raw_row k) _ T hit
  have path (u : Nat) (hu : u ≤ t) :
      (machine k).run u (initialConfig (machine k) B v)=
        mapOld k (SmallIngress.machine.run u (initialConfig SmallIngress.machine B v)) := by
    have p := prefixPath u hu
    rw [er_initial,map_er] at p
    exact p
  refine ⟨t,ht,same.trans old,path,?_⟩
  intro u hu
  have no := first u hu
  change ¬(_=345 ∨ _=346) at no
  have state := congrArg (fun c => c.state.val) (path u (by omega))
  dsimp only at state
  change ((machine k).run u (initialConfig (machine k) B v)).state.val=
    (SmallIngress.machine.run u (initialConfig SmallIngress.machine B v)).state.val at state
  rw [state]
  tauto
private theorem fixed_run (A : UniformTM) {N B : Nat} (c : Config A.stateCount N B)
    (fixed : A.stepConfig c=c) (t : Nat) : A.run t c=c := by
  induction t with
  | zero => simp only [UniformTM.run]
  | succ t ih => simpa only [UniformTM.run,ih] using fixed

private theorem keepS (A : UniformTM) {N B : Nat} (s d : Fin A.stateCount)
    (V : Fin (tapeLength N B) → Option Bool) (h : Fin (tapeLength N B))
    (row : A.step s (V h)=(d,V h,.stay)) :
    A.stepConfig ⟨s,h,V⟩=⟨d,h,V⟩ := by
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · change moveHead h _=h; rw [row]; rfl
  · funext i
    change (if i=h then (A.step s (V h)).2.1 else V i)=V i
    rw [row]; split <;> rename_i e
    · subst i; rfl
    · rfl
private theorem writeR (A : UniformTM) {N B : Nat} (s d : Fin A.stateCount)
    (V : Fin (tapeLength N B) → Option Bool) (h : Nat)
    (hh : h < tapeLength N B) (hd : h+1 < tapeLength N B) (v : Option Bool)
    (row : A.step s (V ⟨h,hh⟩)=(d,v,.right)) :
    A.stepConfig ⟨s,⟨h,hh⟩,V⟩=
      ⟨d,⟨h+1,hd⟩,fun i => if i.val=h then v else V i⟩ := by
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · change moveHead ⟨h,hh⟩ _=⟨h+1,hd⟩; rw [row]; simp [moveHead,hd]
  · funext i
    change (if i=⟨h,hh⟩ then (A.step s (V ⟨h,hh⟩)).2.1 else V i)=_
    rw [row]
    simp only [Fin.ext_iff]
/-- The existing literal physical branch, on the new producer288 composite. -/
theorem physical_two (k : Nat) {N B : Nat} (V : Nat → Option Bool) (p : Nat)
    (hp : p < tapeLength N B) (hp1 : p+1 < tapeLength N B) (b : Bool) (bit : V p=some b) :
    (machine k).run 1 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 58,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 64,⟨p,hp⟩,fun i => V i.val⟩ ∧
    (machine k).run 2 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 58,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (if b then 83 else 68),⟨p+1,hp1⟩,
            fun i => if i.val=p then none else V i.val⟩ := by
  have one := keepS (Cursor.machine k) (Cursor.q k 58) (Cursor.q k 64)
    (fun i => V i.val) ⟨p,hp⟩ (by simpa only [bit] using (SuffixCap.entry_rows k b).1)
  have two := writeR (Cursor.machine k) (Cursor.q k 64) (Cursor.q k (if b then 83 else 68))
    (fun i => V i.val) p hp hp1 none (by simpa only [bit] using (SuffixCap.entry_rows k b).2)
  constructor
  · change (SmallIngress.producer.seq (Cursor.machine k)).run 1 _=_
    rw [UniformTM.seq_run_right]
    simpa only [UniformTM.run] using congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) one
  · change (SmallIngress.producer.seq (Cursor.machine k)).run 2 _=_
    rw [UniformTM.seq_run_right]
    simp only [UniformTM.run]
    rw [one,two]
/-- EOF is blank, distinct from a physical false; both literal rows preserve it. -/
theorem eof_two (k : Nat) {N B : Nat} (V : Nat → Option Bool) (p : Nat)
    (hp : p < tapeLength N B) (hp1 : p+1 < tapeLength N B) (blank : V p=none) :
    (machine k).run 1 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 57,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 65,⟨p,hp⟩,fun i => V i.val⟩ ∧
    (machine k).run 2 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 57,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 66,⟨p+1,hp1⟩,fun i => V i.val⟩ := by
  have row1 : (Cursor.machine k).step (Cursor.q k 57) none=(Cursor.q k 65,none,.stay) := rfl
  have row2 : (Cursor.machine k).step (Cursor.q k 65) none=(Cursor.q k 66,none,.right) := rfl
  have one := keepS (Cursor.machine k) (Cursor.q k 57) (Cursor.q k 65)
    (fun i => V i.val) ⟨p,hp⟩ (by simpa only [blank] using row1)
  have two := writeR (Cursor.machine k) (Cursor.q k 65) (Cursor.q k 66)
    (fun i => V i.val) p hp hp1 none (by simpa only [blank] using row2)
  have tape : (fun i : Fin (tapeLength N B) => if i.val=p then none else V i.val)=
      (fun i : Fin (tapeLength N B) => V i.val) := by
    funext i; split <;> rename_i h
    · simpa only [h] using blank.symm
    · rfl
  rw [tape] at two
  constructor
  · change (SmallIngress.producer.seq (Cursor.machine k)).run 1 _=_
    rw [UniformTM.seq_run_right]
    simpa only [UniformTM.run] using congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) one
  · change (SmallIngress.producer.seq (Cursor.machine k)).run 2 _=_
    rw [UniformTM.seq_run_right]
    simp only [UniformTM.run]
    rw [one,two]

private theorem actual_source {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z) :
    let U := Body.extend (Body.installedTape (SmallIngress.prepared
      (FixedRawLengthFence.allocation (pairLength a m)) x w z n) (a+m+z+2) n)
    let V := Stream.Target.image U (a+m) z n (9+2*z) (2^n) (2^n) false
    (∀ i, 9+2*z ≤ i → i < a+m → ∃ b, V i=some b) ∧ V (a+m)=none := by
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  have gammaSupport := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  obtain ⟨room,_scratch,hF,_fence⟩ := Stream.raw_budget_cells x w gamma cap
  change S+z+n+3 < FixedRawLengthFence.fencePos R at room
  change FixedRawLengthFence.fencePos R < tapeLength R B at hF
  have fit : S+z+n+3 < tapeLength R B := room.trans hF
  have low (i : Nat) (hi : i ≤ S) (above : 7 < i) :
      V i=FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,by change i < tapeLength R B; omega⟩ := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    change U i=_
    dsimp only [U,Body.extend]
    rw [dif_pos (by change i < tapeLength R B; omega)]
    dsimp only [Body.installedTape]
    rw [if_neg (by omega)]
    dsimp only [SmallIngress.prepared]
    rw [if_neg (by omega)]
  change (∀ i, 9+2*z ≤ i → i < S → ∃ b, V i=some b) ∧ V S=none
  constructor
  · intro i lo hi
    rw [low i (by omega) (by omega)]
    exact ⟨_,Body.raw_source_after_header x w gamma (FixedRawLengthFence.resource_bounds R).1
      (Nat.le_of_lt cap) ⟨i,by change i < tapeLength R B; omega⟩
      (by change 8+2*z+1 ≤ i; omega) hi⟩
  · change V S=none
    rw [low S le_rfl (by dsimp only [S]; omega)]
    unfold FixedRawLengthFence.countdownTape
    rw [if_neg (by change S ≠ FixedRawLengthFence.fencePos R; omega)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
private theorem cursor_lower (A S r : Nat) (h : min (A+r) S < S) :
    A ≤ min (A+r) S := by omega
private theorem two_clock (R T t : Nat) (price : T ≤ 4096*(R+1)^2) (ht : t ≤ T) :
    t+2 ≤ 8192*(R+1)^2 := by
  have pos : 0 < (R+1)^2 := Nat.pow_pos (by omega)
  omega
/-- Accepted raw ingress of every arity, all paid configurations, the first live
handoff and its two executed Cursor rows on the original physical allocation. -/
theorem accepted_raw (k : Nat) : Target.AcceptedRaw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,z,T,hH,gamma,price,paid,hp,finish⟩ := SmallOrbit.original_accepted_raw k x w accepted
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let n := pr.2.n
  let p := Stream.Target.cursor (9+2*z) S (2^n)
  let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let old := initialConfig SmallIngress.machine B (encodePair x w)
  let raw := initialConfig (machine k) B (encodePair x w)
  have ple : p ≤ S := Nat.min_le_right _ _
  have hp1 : p+1 < tapeLength R B := by
    change S+z+n+3 < tapeLength R B at hH
    omega
  have hs : (Stream.q (if p=S then 57 else 58)).val=57 ∨
      (Stream.q (if p=S then 57 else 58)).val=58 := by
    split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl
  obtain ⟨t,ht,first,path,absent⟩ := first_raw k (encodePair x w) T
    (Stream.q (if p=S then 57 else 58)) hs ⟨p,hp⟩ (fun i => V i.val) finish
  have endpoint : (machine k).run t raw=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ := by
    rw [path t le_rfl,first,map_right]
    split_ifs <;> rfl
  have stopped : SmallIngress.machine.stepConfig (SmallIngress.machine.run t old)=
      SmallIngress.machine.run t old := by
    apply old_inert
    rw [first]
    change 288+(Stream.q (if p=S then 57 else 58)).val=345 ∨
      288+(Stream.q (if p=S then 57 else 58)).val=346
    rcases hs with h | h <;> rw [h] <;> omega
  have width : n ≤ S := by
    have lt := Nat.lt_two_pow_self (n := n)
    change 2^n ≤ S at table
    omega
  have cap := AcceptedBody.strict_capacity x w gamma width
  obtain ⟨source,eof⟩ := actual_source x w gamma cap
  refine ⟨pr,parsed,table,z,T,t,hH,gamma,price,ht,two_clock R T t price ht,?_⟩
  refine ⟨hp,hp1,finish,first,path,absent,?_,endpoint,?_,?_⟩
  · intro r hr
    obtain ⟨u,hu,pay⟩ := paid r hr
    have before : u < t := by
      by_contra no
      have later : SmallIngress.machine.run u old=SmallIngress.machine.run t old := by
        rw [show u=t+(u-t) by omega,UniformTM.run_add]
        exact fixed_run SmallIngress.machine _ stopped _
      have heads := congrArg (fun c => c.head.val) (pay.symm.trans (later.trans first))
      change S+z+n+3=p at heads
      omega
    refine ⟨u,before,?_⟩
    rw [path u (by omega),pay,map_right]
  · intro eofAt
    have blank : V p=none := by change p=S at eofAt; simpa only [eofAt] using eof
    have ep := endpoint
    change p=S at eofAt
    rw [if_pos eofAt] at ep
    obtain ⟨one,two⟩ := eof_two k V p hp hp1 blank
    exact ⟨blank,by rw [UniformTM.run_add,ep]; exact one,
      by rw [UniformTM.run_add,ep]; exact two⟩
  · intro physical
    have pp : p < S := physical
    have above : 9+2*z ≤ p := cursor_lower (9+2*z) S (2^n) pp
    obtain ⟨b,bit⟩ := source p above physical
    have ep := endpoint
    rw [if_neg (Nat.ne_of_lt pp)] at ep
    obtain ⟨one,two⟩ := physical_two k V p hp hp1 b bit
    exact ⟨b,bit,by rw [UniformTM.run_add,ep]; exact one,
      by rw [UniformTM.run_add,ep]; exact two⟩
end AllArityCursor
