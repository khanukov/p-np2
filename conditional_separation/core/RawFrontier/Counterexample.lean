import RawFrontier.Capacity
import Complexity.PrivateInterfaceLookupResolvedSuffixFrontier
namespace RawFrontier
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
open FixedGammaTargetRegisterDecrement (borrow decBit)
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private def sample : Bitstring 11 := fun i =>
  i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
private abbrev empty : Bitstring 0 := Fin.elim0
private abbrev T := FixedRawLengthFence.countdownTape 9216 sample empty 2 0 3
private abbrev V := Body.installedTape T 15 3
private abbrev startBody : Config Stream.machine.stateCount 23 9216 :=
  ⟨Stream.machine.start,⟨15,by decide⟩,T⟩
private abbrev loopBody : Config Stream.machine.stateCount 23 9216 :=
  ⟨Stream.q 5,⟨0,by decide⟩,V⟩
private theorem install : Stream.machine.run 5 startBody=
    ⟨Stream.q 2,⟨19,by decide⟩,V⟩ := by
  run_tac do
    let env ← getEnv
    let names ← PartAPrivateSuffixFrontier.selectBatch [(`Stream.Kernel,`Stream.install_exact)]
    let src := "(
      apply OLD 15 3 startBody (by decide) rfl rfl (by decide) (by decide)
      intro i lo hi
      have cases : i.val=16 ∨ i.val=17 ∨ i.val=18 := by omega
      rcases cases with h | h | h
      · have eq : i=⟨16,by decide⟩ := Fin.ext h
        subst i
        decide
      · have eq : i=⟨17,by decide⟩ := Fin.ext h
        subst i
        decide
      · have eq : i=⟨18,by decide⟩ := Fin.ext h
        subst i
        decide)"
    let ast ← ofExcept (Parser.runParserCategory env `tactic src)
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent && stx.getId.toString == "OLD" then mkIdent names.head! else stx)
private theorem keep (s s' : Fin Stream.machine.stateCount) (h h' : Fin (tapeLength 23 9216))
    (row : Stream.machine.step s (V h)=(s',V h,.left)) (dest : moveHead h .left=h') :
    Stream.machine.stepConfig (⟨s,h,V⟩ : Config Stream.machine.stateCount 23 9216)=⟨s',h',V⟩ := by
  refine Config.ext_parts (congrArg Prod.fst row) ?_ ?_
  · change moveHead h (Stream.machine.step s (V h)).2.2=h'
    rw [row]; exact dest
  · funext i
    change (if i=h then (Stream.machine.step s (V h)).2.1 else V i)=V i
    rw [row]
    split_ifs with hi
    · subst i; rfl
    · rfl
private theorem body_run : Stream.machine.run 24 startBody=loopBody := by
  have p0 := install
  have step1 := keep (Stream.q 2) (Stream.q 3) ⟨19,by decide⟩ ⟨18,by decide⟩ (by decide) (by decide)
  have p1 : Stream.machine.run 6 startBody=⟨Stream.q 3,⟨18,by decide⟩,V⟩ := by
    rw [UniformTM.run,p0]
    exact step1
  have step2 := keep (Stream.q 3) (Stream.q 3) ⟨18,by decide⟩ ⟨17,by decide⟩ (by decide) (by decide)
  have p2 : Stream.machine.run 7 startBody=⟨Stream.q 3,⟨17,by decide⟩,V⟩ := by
    rw [UniformTM.run,p1]
    exact step2
  have step3 := keep (Stream.q 3) (Stream.q 3) ⟨17,by decide⟩ ⟨16,by decide⟩ (by decide) (by decide)
  have p3 : Stream.machine.run 8 startBody=⟨Stream.q 3,⟨16,by decide⟩,V⟩ := by
    rw [UniformTM.run,p2]
    exact step3
  have step4 := keep (Stream.q 3) (Stream.q 3) ⟨16,by decide⟩ ⟨15,by decide⟩ (by decide) (by decide)
  have p4 : Stream.machine.run 9 startBody=⟨Stream.q 3,⟨15,by decide⟩,V⟩ := by
    rw [UniformTM.run,p3]
    exact step4
  have step5 := keep (Stream.q 3) (Stream.q 4) ⟨15,by decide⟩ ⟨14,by decide⟩ (by decide) (by decide)
  have p5 : Stream.machine.run 10 startBody=⟨Stream.q 4,⟨14,by decide⟩,V⟩ := by
    rw [UniformTM.run,p4]
    exact step5
  have step6 := keep (Stream.q 4) (Stream.q 4) ⟨14,by decide⟩ ⟨13,by decide⟩ (by decide) (by decide)
  have p6 : Stream.machine.run 11 startBody=⟨Stream.q 4,⟨13,by decide⟩,V⟩ := by
    rw [UniformTM.run,p5]
    exact step6
  have step7 := keep (Stream.q 4) (Stream.q 4) ⟨13,by decide⟩ ⟨12,by decide⟩ (by decide) (by decide)
  have p7 : Stream.machine.run 12 startBody=⟨Stream.q 4,⟨12,by decide⟩,V⟩ := by
    rw [UniformTM.run,p6]
    exact step7
  have step8 := keep (Stream.q 4) (Stream.q 4) ⟨12,by decide⟩ ⟨11,by decide⟩ (by decide) (by decide)
  have p8 : Stream.machine.run 13 startBody=⟨Stream.q 4,⟨11,by decide⟩,V⟩ := by
    rw [UniformTM.run,p7]
    exact step8
  have step9 := keep (Stream.q 4) (Stream.q 5) ⟨11,by decide⟩ ⟨10,by decide⟩ (by decide) (by decide)
  have p9 : Stream.machine.run 14 startBody=⟨Stream.q 5,⟨10,by decide⟩,V⟩ := by
    rw [UniformTM.run,p8]
    exact step9
  have step10 := keep (Stream.q 5) (Stream.q 5) ⟨10,by decide⟩ ⟨9,by decide⟩ (by decide) (by decide)
  have p10 : Stream.machine.run 15 startBody=⟨Stream.q 5,⟨9,by decide⟩,V⟩ := by
    rw [UniformTM.run,p9]
    exact step10
  have step11 := keep (Stream.q 5) (Stream.q 5) ⟨9,by decide⟩ ⟨8,by decide⟩ (by decide) (by decide)
  have p11 : Stream.machine.run 16 startBody=⟨Stream.q 5,⟨8,by decide⟩,V⟩ := by
    rw [UniformTM.run,p10]
    exact step11
  have step12 := keep (Stream.q 5) (Stream.q 5) ⟨8,by decide⟩ ⟨7,by decide⟩ (by decide) (by decide)
  have p12 : Stream.machine.run 17 startBody=⟨Stream.q 5,⟨7,by decide⟩,V⟩ := by
    rw [UniformTM.run,p11]
    exact step12
  have step13 := keep (Stream.q 5) (Stream.q 5) ⟨7,by decide⟩ ⟨6,by decide⟩ (by decide) (by decide)
  have p13 : Stream.machine.run 18 startBody=⟨Stream.q 5,⟨6,by decide⟩,V⟩ := by
    rw [UniformTM.run,p12]
    exact step13
  have step14 := keep (Stream.q 5) (Stream.q 5) ⟨6,by decide⟩ ⟨5,by decide⟩ (by decide) (by decide)
  have p14 : Stream.machine.run 19 startBody=⟨Stream.q 5,⟨5,by decide⟩,V⟩ := by
    rw [UniformTM.run,p13]
    exact step14
  have step15 := keep (Stream.q 5) (Stream.q 5) ⟨5,by decide⟩ ⟨4,by decide⟩ (by decide) (by decide)
  have p15 : Stream.machine.run 20 startBody=⟨Stream.q 5,⟨4,by decide⟩,V⟩ := by
    rw [UniformTM.run,p14]
    exact step15
  have step16 := keep (Stream.q 5) (Stream.q 5) ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (by decide)
  have p16 : Stream.machine.run 21 startBody=⟨Stream.q 5,⟨3,by decide⟩,V⟩ := by
    rw [UniformTM.run,p15]
    exact step16
  have step17 := keep (Stream.q 5) (Stream.q 5) ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide) (by decide)
  have p17 : Stream.machine.run 22 startBody=⟨Stream.q 5,⟨2,by decide⟩,V⟩ := by
    rw [UniformTM.run,p16]
    exact step17
  have step18 := keep (Stream.q 5) (Stream.q 5) ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (by decide)
  have p18 : Stream.machine.run 23 startBody=⟨Stream.q 5,⟨1,by decide⟩,V⟩ := by
    rw [UniformTM.run,p17]
    exact step18
  have step19 := keep (Stream.q 5) (Stream.q 5) ⟨1,by decide⟩ ⟨0,by decide⟩ (by decide) (by decide)
  have p19 : Stream.machine.run 24 startBody=⟨Stream.q 5,⟨0,by decide⟩,V⟩ := by
    rw [UniformTM.run,p18]
    exact step19
  exact p19
private theorem body_fixed : Stream.machine.stepConfig loopBody=loopBody :=
  keep (Stream.q 5) (Stream.q 5) ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide) (by decide)
private theorem producer_reaches : ∃ tp, tp ≤ 73728 ∧
    (∀ u, u < tp → (SmallIngress.producer.run u (initialConfig SmallIngress.producer 9216
      (encodePair sample empty))).state≠SmallIngress.producer.accept) ∧
    SmallIngress.producer.run tp (initialConfig SmallIngress.producer 9216 (encodePair sample empty))=
      ⟨SmallIngress.producer.accept,⟨15,by decide⟩,T⟩ := by
  have tag : FixedContentTagGate.tagMatches (Fin.append sample empty)=true := by decide
  have gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append sample empty)=some 2 := by decide
  obtain ⟨C,q,price,first,_⟩ := FixedGammaPayloadDispatcherFirstArrival.tagged_strict_first_terminal
    (B := 9216) sample empty tag
  have digits : ∀ j, j ≤ 2 → (3:Nat).testBit (2-j)=decBit sample empty 2 (borrow sample empty 2) j := by
    intro j hj
    interval_cases j <;> decide
  have high : ∀ b, 2 < b → (3:Nat).testBit b=false :=
    (FixedGammaTargetUnaryCountdownIteration.high_iff_lt 3 2).2 (by decide)
  have old := FixedRawLengthFence.raw_fenced_countdown_success_exact sample empty
    (by decide : 2*pairLength 11 0+2 ≤ 9216) tag gamma (by decide) first digits high (by decide) 0
  simp only [Nat.add_zero] at old
  have safe : (FixedRawLengthFence.prefixed.run
      (FixedRawLengthFence.countdownSuccessClock 11 0 2 C (borrow sample empty 2) 3)
      (initialConfig FixedRawLengthFence.prefixed 9216 (encodePair sample empty))).state≠
      FixedRawLengthFence.prefixed.reject := by rw [old]; exact FixedRawLengthFence.prefixed.accept_ne_reject
  have transferred := SmallIngress.preserves_nonreject _ _ safe
  change SmallIngress.producer.run _ (initialConfig SmallIngress.producer 9216 (encodePair sample empty))=_ at transferred
  rw [old] at transferred
  have endpoint : SmallIngress.producer.run
      (FixedRawLengthFence.countdownSuccessClock 11 0 2 C (borrow sample empty 2) 3)
      (initialConfig SmallIngress.producer 9216 (encodePair sample empty))=
        ⟨SmallIngress.producer.accept,⟨15,by decide⟩,T⟩ := transferred
  have bound : FixedRawLengthFence.countdownSuccessClock 11 0 2 C (borrow sample empty 2) 3 ≤ 73728 :=
    (FixedRawLengthFence.countdown_clock_bound (by decide : 9+2 ≤ 11+0) (by decide)
      (FixedGammaTargetRegisterDecrement.borrow_pins sample empty 2).1 price (by decide : 3 ≤ FixedRawLengthFence.capacity 11 0 2)).1
  obtain ⟨tp,ht,firstAccept,arrived⟩ := Body.first_accept_whole SmallIngress.producer
    (initialConfig SmallIngress.producer 9216 (encodePair sample empty)) _ _ endpoint rfl
  exact ⟨tp,ht.trans bound,firstAccept,arrived⟩
private theorem old_reaches : ∃ t, t ≤ 73752 ∧
    SmallIngress.machine.run t (initialConfig SmallIngress.machine 9216 (encodePair sample empty))=
      SmallIngress.producer.seqEmbedRight Stream.machine loopBody := by
  obtain ⟨tp,price,first,arrived⟩ := producer_reaches
  have hand := SmallIngress.producer.seq_handoff Stream.machine
    (initialConfig SmallIngress.producer 9216 (encodePair sample empty)) first (by rw [arrived]) 24
  change SmallIngress.machine.run (tp+24) (initialConfig SmallIngress.machine 9216 (encodePair sample empty))=_ at hand
  rw [arrived] at hand
  change SmallIngress.machine.run (tp+24) (initialConfig SmallIngress.machine 9216 (encodePair sample empty))=
    SmallIngress.producer.seqEmbedRight Stream.machine (Stream.machine.run 24 startBody) at hand
  rw [body_run] at hand
  exact ⟨tp+24,by omega,hand⟩
private theorem fixed_run (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (fixed : M.stepConfig c=c) (t : Nat) : M.run t c=c := by
  induction t with
  | zero => simp only [UniformTM.run]
  | succ t ih => rw [UniformTM.run,ih,fixed]
private theorem work_fixed {N B : Nat} (c : Config SmallIngress.machine.stateCount N B)
    (work : c.state.val=345 ∨ c.state.val=346) : SmallIngress.machine.stepConfig c=c := by
  run_tac do
    let env ← getEnv
    let names ← PartAPrivateSuffixFrontier.selectBatch [(`AllArityCursor.Runtime,`AllArityCursor.old_inert)]
    let ast ← ofExcept (Parser.runParserCategory env `tactic "(exact OLD c work)")
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent && stx.getId.toString == "OLD" then mkIdent names.head! else stx)
private theorem replay (k : Nat) {N B : Nat} (y : Bitstring N) (t : Nat)
    (outside : ¬((SmallIngress.machine.run t (initialConfig SmallIngress.machine B y)).state.val=345 ∨
      (SmallIngress.machine.run t (initialConfig SmallIngress.machine B y)).state.val=346)) :
    (AllArityCursor.machine k).run t (initialConfig (AllArityCursor.machine k) B y)=
      AllArityCursor.mapOld k (SmallIngress.machine.run t (initialConfig SmallIngress.machine B y)) := by
  run_tac do
    let env ← getEnv
    let keys : List String := ["er","exits","old_inert","raw_row","er_initial","map_er"]
    let selected ← PartAPrivateSuffixFrontier.selectBatch [
      (`AllArityCursor.Runtime,`AllArityCursor.er),(`AllArityCursor.Runtime,`AllArityCursor.exits),
      (`AllArityCursor.Runtime,`AllArityCursor.old_inert),(`AllArityCursor.Runtime,`AllArityCursor.raw_row),
      (`AllArityCursor.Runtime,`AllArityCursor.er_initial),(`AllArityCursor.Runtime,`AllArityCursor.map_er)]
    let mapping := (keys.zip selected).map fun (key,n) => ("OLD_"++key,n)
    let src := "(
      have h := Cursor.Transport.avoid_changed_rows SmallIngress.machine (AllArityCursor.machine k)
        (OLD_er k) OLD_exits (fun c hc => OLD_old_inert c hc) (OLD_raw_row k)
        (initialConfig SmallIngress.machine B y) t outside
      rw [OLD_er_initial,OLD_map_er] at h
      exact h)"
    let ast ← ofExcept (Parser.runParserCategory env `tactic src)
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1==stx.getId.toString) with
        | some (_,name) => mkIdent name
        | none => stx
      else stx)
private theorem old_fixed : SmallIngress.machine.stepConfig
    (SmallIngress.producer.seqEmbedRight Stream.machine loopBody)=
    SmallIngress.producer.seqEmbedRight Stream.machine loopBody := by
  change (SmallIngress.producer.seq Stream.machine).stepConfig _=_
  rw [UniformTM.seq_stepConfig_right,body_fixed]
private theorem old_avoids (t0 : Nat)
    (hit : SmallIngress.machine.run t0 (initialConfig SmallIngress.machine 9216 (encodePair sample empty))=
      SmallIngress.producer.seqEmbedRight Stream.machine loopBody) :
    ∀ u, ¬((SmallIngress.machine.run u (initialConfig SmallIngress.machine 9216 (encodePair sample empty))).state.val=327 ∨
      (SmallIngress.machine.run u (initialConfig SmallIngress.machine 9216 (encodePair sample empty))).state.val=328 ∨
      (SmallIngress.machine.run u (initialConfig SmallIngress.machine 9216 (encodePair sample empty))).state.val=345 ∨
      (SmallIngress.machine.run u (initialConfig SmallIngress.machine 9216 (encodePair sample empty))).state.val=346) := by
  intro u hu
  let c := initialConfig SmallIngress.machine 9216 (encodePair sample empty)
  by_cases before : u ≤ t0
  · have same : SmallIngress.machine.run t0 c=SmallIngress.machine.run u c := by
      rw [show t0=u+(t0-u) by omega,UniformTM.run_add]
      apply fixed_run
      rcases hu with accept | reject | work
      · apply SmallIngress.machine.stepConfig_accept
        exact Fin.ext accept
      · apply SmallIngress.machine.stepConfig_reject
        exact Fin.ext reject
      · exact work_fixed _ work
    have bad := congrArg (fun c => c.state.val) (same.symm.trans hit)
    change (SmallIngress.machine.run u c).state.val=293 at bad
    have hu' : (SmallIngress.machine.run u c).state.val=327 ∨
      (SmallIngress.machine.run u c).state.val=328 ∨
      (SmallIngress.machine.run u c).state.val=345 ∨
      (SmallIngress.machine.run u c).state.val=346 := hu
    rw [bad] at hu'
    omega
  · have same : SmallIngress.machine.run u c=SmallIngress.producer.seqEmbedRight Stream.machine loopBody := by
      rw [show u=t0+(u-t0) by omega,UniformTM.run_add,hit]
      exact fixed_run _ _ old_fixed _
    rw [same] at hu
    change (293:Nat)=327 ∨ 293=328 ∨ 293=345 ∨ 293=346 at hu
    omega
/-- A genuine raw word stalls on an occupied origin cell. Every prior and future
state avoids the literal frontier. This disproves ANY all-input frontier clock. -/
theorem raw_stalls (k : Nat) :
    let x : Bitstring 11 := fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
    let c := initialConfig (AllArityCursor.machine k) 9216 (encodePair x (Fin.elim0 : Bitstring 0))
    (∀ u, ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject ∧
      ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57) ∧
      ((AllArityCursor.machine k).run u c).state≠SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58) ∧
      ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept) ∧
    ∃ t, t ≤ 73752 ∧
      (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k 5,⟨0,by decide⟩,Body.installedTape (FixedRawLengthFence.countdownTape 9216 x Fin.elim0 2 0 3) 15 3⟩ ∧
      (AllArityCursor.machine k).stepConfig ((AllArityCursor.machine k).run t c)=
        (AllArityCursor.machine k).run t c ∧
      (∀ s, (AllArityCursor.machine k).run (t+s) c=(AllArityCursor.machine k).run t c) := by
  dsimp only
  obtain ⟨t0,price,hit⟩ := old_reaches
  have avoid := old_avoids t0 hit
  have path (u : Nat) := replay k (encodePair sample empty) u (by
    intro h
    exact avoid u (Or.inr (Or.inr h)))
  let c := initialConfig (AllArityCursor.machine k) 9216 (encodePair sample empty)
  constructor
  · intro u
    have val := congrArg (fun c => c.state.val) (path u)
    change ((AllArityCursor.machine k).run u c).state.val=
      (SmallIngress.machine.run u (initialConfig SmallIngress.machine 9216 (encodePair sample empty))).state.val at val
    have no := avoid u
    refine ⟨?_,?_,?_,?_⟩
    all_goals
      intro h
      have e := congrArg Fin.val h
      change ((AllArityCursor.machine k).run u c).state.val=_ at e
      simp only [(AllArityCursor.control_values k).1,(AllArityCursor.control_values k).2.1,
        (AllArityCursor.control_values k).2.2.1,(AllArityCursor.control_values k).2.2.2] at e
      rw [val] at e
      tauto
  · have endpoint := path t0
    rw [hit] at endpoint
    have same : (AllArityCursor.machine k).run (t0+1) c=(AllArityCursor.machine k).run t0 c := by
      rw [path (t0+1),path t0,UniformTM.run_add,hit]
      rw [fixed_run _ _ old_fixed 1]
    have fixed : (AllArityCursor.machine k).stepConfig ((AllArityCursor.machine k).run t0 c)=
        (AllArityCursor.machine k).run t0 c := by
      simpa only [UniformTM.run] using same
    refine ⟨t0,price,?_,fixed,?_⟩
    · refine endpoint.trans ?_
      refine Config.ext_parts ?_ rfl rfl
      apply Fin.ext
      change 293=288+5 % Cursor.stateCount k
      rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
    · intro s
      rw [UniformTM.run_add]
      exact fixed_run _ _ fixed s
/-- The frozen unconditional target is false for the unchanged literal table. -/
theorem frontier_impossible (k : Nat) : ¬Target.Frontier k := by
  intro full
  obtain ⟨t,_price,hit,_first,_safe,_sound⟩ := full sample empty
  have no := (raw_stalls k).1 t
  rcases hit with h | h | h
  · exact no.1 h
  · exact no.2.1 h
  · exact no.2.2.1 h
theorem sample_relation_false (k : Nat) :
    PartAEndpoint.thresholdContentWitnessRelation k 11 0
      (fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10) Fin.elim0=false := by
  cases rel : PartAEndpoint.thresholdContentWitnessRelation k 11 0 sample empty with
  | false => exact rel
  | true =>
    exfalso
    obtain ⟨_pr,_parsed,_table,_z,t,_hH,_gamma,_price,_hp,pre,_prefix,_physical,_eof⟩ :=
      AllArityWorkspace.accepted_raw k sample empty rel
    have e := congrArg Config.state pre
    have no := (raw_stalls k).1 t
    split_ifs at e
    · exact no.2.1 e
    · exact no.2.2.1 e
end RawFrontier
