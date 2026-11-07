import CarryReadyCompletion.Native
namespace CarryReadyCompletion
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private theorem physical_event (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    (pr : Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q))
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (phys : min (9+2*z+2^pr.2.n) (a+m)     <     a+m)
    (over : a+m-min (9+2*z+2^pr.2.n) (a+m)     <     Cursor.Target.W k pr.2.n) :
    let c:=initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t, (∀ u, u     <     t      →      ((AllArityCursor.machine k).run u c).state.val     <     288+430+93*k)      ∧
      (((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 250)      ∨
       ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 304)      ∨
       ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (798+93*k))) := by
  fromDonor "PowerDriver.Seed" "PowerDriver" "seed_ceiling" =>
    obtain ⟨pr',parsed',table,z',hH,gamma',_eof,physical⟩:=OLD k x w accepted
  have pe : pr'=pr:=Option.some.inj (parsed'.symm.trans parsed)
  subst pr'
  have ze : z'=z:=Option.some.inj (gamma'.symm.trans gamma)
  subst z'
  let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S; let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  obtain ⟨t,h,_price,fit,reached,prior,_⟩:=physical phys
  change F+5*r+n+7   <   tapeLength R B at fit
  have rp : 0   <   r:=Nat.sub_pos_of_lt phys
  by_cases fits : bitLength pr.2.n    ≤    a+m-min (9+2*z+2^pr.2.n) (a+m)
  · have width : n     ≤     S := by have lt:=Nat.lt_two_pow_self (n:=n); change 2^n     ≤     S at table; omega
    have cap:=AcceptedBody.strict_capacity x w gamma width
    have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
    fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "actual_cells" => obtain ⟨cf,_short,fresh⟩:=OLD x w gamma cap rows
    fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.arena" => have arena:=OLD cf
    fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.sep" => have sep:=OLD cf
    fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.right" => have right:=OLD cf
    fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.marks" => have marks:=OLD cf
    fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.gap" => have gap:=OLD cf
    fromDonor "AllArityBitLength.Raw" "AllArityBitLength" "Cells.fence" => have fence:=OLD cf
    have H : L+n+1=S+z+n+3 := by dsimp only [L]; omega
    have fr : (by fromDonor "PowerDriver.Kernel" "PowerDriver" "Frame" => exact OLD Z L n (2^n) F r) := by
      fromDonor "PowerDriver.Raw" "PowerDriver" "prepared_seed" =>
        exact OLD L n (2^n) F r V rp fits
          (by positivity) (by change S+z+n+3+2^n     <     F at arena; omega) sep (by rw [H]; exact right)
          (by intro i lo hi; exact marks i (by omega) (by omega))
          (by intro i lo hi; exact gap i (by omega) hi) fence
          (by intro i lo hi; exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
    fromDonor "PowerDriver.Kernel" "PowerDriver" "driver" => obtain ⟨d,_phase,branch⟩:=OLD (k:=k) Z fr rp
    have headD3 : F+2*r+n+4     <     tapeLength R B:=lt_of_le_of_lt (by omega : F+2*r+n+4     ≤     F+5*r+n+7) fit
    have seed : (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k 329,⟨F+2*r+n+4,headD3⟩,fun i => Z i.val⟩ := by simpa only [if_pos fits] using reached
    rcases branch with ⟨ok,path⟩|⟨j,a0,e,hj,ha,he,eq,path⟩
    all_goals
      fromDonor "PowerDriver.Kernel" "PowerDriver" "Path.execute" => have ex:=OLD path fit
      fromDonor "PowerDriver.Kernel" "PowerDriver" "Path.first" => have fs:=OLD path fit
      have before : ∀ u, u     <     t+d      →      ((AllArityCursor.machine k).run u c).state.val     <     288+329+82*k := by
        intro u hu
        by_cases early : u     <     t
        · exact (prior u early).trans_le (by omega)
        · rw [show u=t+(u-t) by omega,UniformTM.run_add,seed]
          fromDonor "FullWeight.Raw" "FullWeight" "right_run" => rw [OLD]
          change 288+_     <     288+329+82*k
          exact (Nat.add_lt_add_left (fs (u-t) (by omega)) 288).trans_le (by omega)
    · have powerRun : (AllArityCursor.machine k).run (t+d) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (329+82*k),⟨F+2*r+n+4,headD3⟩,fun i => CappedWeight.Target.image Z L n F r (bitLength n) (n^k) 0 0 0 i.val⟩ := by
        rw [UniformTM.run_add,seed]
        fromDonor "FullWeight.Raw" "FullWeight" "right_run" => rw [OLD]
        exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) ex
      fromDonor "FullWeight.Loops" "FullWeight" "tail" => obtain ⟨v,_pv,tailBranch⟩:=OLD (k:=k) Z fr (bitLength n) (n^k) fits ok
      rcases tailBranch with ⟨final,_⟩|⟨v2,v3,v4,v5,_caps,tailPath⟩
      · exact False.elim (Nat.not_lt_of_ge final over)
      · fromDonor "FullWeight.Kernel" "FullWeight" "Path.execute" => have tailEx:=OLD tailPath fit
        fromDonor "FullWeight.Kernel" "FullWeight" "Path.first" => have tailFirst:=OLD tailPath fit
        refine ⟨t+d+v,?_,Or.inr (Or.inr ?_)⟩
        · intro u hu
          by_cases early : u     <     t+d
          · exact (before u early).trans_le (by omega)
          · rw [show u=(t+d)+(u-(t+d)) by omega,UniformTM.run_add,powerRun]
            fromDonor "FullWeight.Raw" "FullWeight" "right_run" => rw [OLD]
            change 288+_     <     288+430+93*k
            exact (Nat.add_lt_add_left (tailFirst (u-(t+d)) (by omega)) 288).trans_le (by omega)
        · have done : (AllArityCursor.machine k).run (t+d+v) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (798+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1  ≤  F+5*r+n+7) fit⟩,
                fun i => CappedWeight.Target.image Z L n F r v2 v3 v4 v5 0 i.val⟩ := by
            rw [UniformTM.run_add,powerRun]
            fromDonor "FullWeight.Raw" "FullWeight" "right_run" => rw [OLD]
            exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) tailEx
          exact congrArg Config.state done
    · refine ⟨t+d,(by intro u hu; exact (before u hu).trans_le (by omega)),Or.inr (Or.inr ?_)⟩
      have done : (AllArityCursor.machine k).run (t+d) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (798+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1  ≤  F+5*r+n+7) fit⟩,
            fun i => CappedWeight.Target.image Z L n F r (bitLength n) (n^j-a0-1) r 0 (e+1) i.val⟩ := by
        rw [UniformTM.run_add,seed]
        fromDonor "FullWeight.Raw" "FullWeight" "right_run" => rw [OLD]
        exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) ex
      exact congrArg Config.state done
  · refine ⟨t,(by intro u hu; exact (prior u hu).trans_le (by omega)),?_⟩
    have done:=congrArg Config.state reached
    simp only [if_neg fits] at done
    by_cases parity : (a+m-min (9+2*z+2^pr.2.n) (a+m)+1)%2=1
    · exact Or.inl (by simpa only [if_pos parity] using done)
    · exact Or.inr (Or.inl (by simpa only [if_neg parity] using done))
private def CQ (k i : Nat) : Fin (CanonicalLeaf.machine k).stateCount :=
  VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i))
private abbrev Closed (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) : Prop := by
  fromDonor "CarryWindow.Raw" "CarryWindow" "Closed" => exact OLD k s
private def After (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount) : Prop :=
  Closed k s      ∨      ∃ i ∈ ([57,65,66,67,250,251,252,253,304,305,306,307] : List Nat), s=CQ k i
private theorem after_ne {k s} (h : After k s) : s     ≠     CQ k (430+93*k)      ∧      s     ≠     CQ k (613+93*k) := by
  rcases h with closed | ⟨i,mem,eq⟩
  · fromDonor "CarryWindow.Raw" "CarryWindow" "closed_ne" => exact OLD k s closed
  · subst s
    have small : i     ≤     307 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at mem; omega
    have val (j : Nat) (hj : j     <     Cursor.stateCount k) : (CQ k j).val=288+j := by
      change 288+j%Cursor.stateCount k=288+j; rw [Nat.mod_eq_of_lt hj]
    constructor
    all_goals intro bad; have e:=congrArg Fin.val bad
    all_goals rw [val i (by unfold Cursor.stateCount; omega),val _ (by unfold Cursor.stateCount; omega)] at e
    all_goals omega
private theorem route_after (k : Nat) (odd : Bool) (j : Nat) (hj : j    <    4) (b : Option Bool) :
    After k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k)
      ((Cursor.machine k).step (Cursor.q k ((if odd then 250 else 304)+j)) b).1)) := by
  let base:=if odd then 250 else 304
  have mem (v : Nat) (hv : v    <    4) : base+v ∈ ([57,65,66,67,250,251,252,253,304,305,306,307] : List Nat) := by
    cases odd <;> interval_cases v <;> decide
  interval_cases j
  · simp only [Nat.add_zero]
    fromDonor "VirtualReady.Kernel" "VirtualReady" "route_rows" => rw [(OLD k odd b false).1]
    exact Or.inr ⟨base+1,mem 1 (by decide),rfl⟩
  · cases b with
    | none =>
      fromDonor "VirtualReady.Kernel" "VirtualReady" "route_rows" => rw [(OLD k odd none false).2.2.1]
      exact Or.inr ⟨base+2,mem 2 (by decide),rfl⟩
    | some v =>
      fromDonor "VirtualReady.Kernel" "VirtualReady" "route_rows" => rw [(OLD k odd none v).2.1]
      exact Or.inr ⟨base+1,mem 1 (by decide),rfl⟩
  · fromDonor "VirtualReady.Kernel" "VirtualReady" "route_rows" => rw [(OLD k odd b false).2.2.2.1]
    exact Or.inr ⟨base+3,mem 3 (by decide),rfl⟩
  · cases b with
    | none =>
      fromDonor "VirtualReady.Kernel" "VirtualReady" "route_rows" => rw [(OLD k odd none false).2.2.2.2.2]
      exact Or.inl (Or.inr (Or.inr ⟨798,by decide,rfl⟩))
    | some v =>
      fromDonor "VirtualReady.Kernel" "VirtualReady" "route_rows" => rw [(OLD k odd none v).2.2.2.2.1]
      exact Or.inr ⟨base+3,mem 3 (by decide),rfl⟩
run_cmd do
  for key in ["decode","program"] do
    let ns:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith (".Cursor."++key)
    unless ns.length=1 do throwError "Nonunique immutable small-row term {key}: {ns}"
    logInfo m!"private-term|{ns.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous ("cursor_"++key)) ns.head! :: st.openDecls}
private theorem eof_decode (k : Nat) (codes : Array Nat) (i : Nat)
    (member : i ∈ ([57,65,66,67] : List Nat)) (b : Option Bool) :
    After k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k)
      (cursor_decode k codes (Cursor.q k i) b).1)) := by
  have small : i ≤ 67 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
  have val : (Cursor.q k i).val=i := by
    change i%Cursor.stateCount k=i; rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
  dsimp only [cursor_decode]
  rw [val]
  have readyEq : Cursor.mReady k ⟨2,by decide⟩=Cursor.q k (936+93*k) := by
    change Cursor.q k (64+265+82*k+1+11*k+604+2)=Cursor.q k (936+93*k)
    congr 1
    omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  all_goals cases b
  all_goals try cases (by assumption : Bool)
  all_goals dsimp only
  all_goals first
    | (right; refine ⟨_,?_,rfl⟩; decide)
    | (left; left; rfl)
    | (rw [readyEq]; left; right; right; exact ⟨936,by decide,rfl⟩)
private theorem eof_after (k : Nat) (i : Nat) (member : i ∈ ([57,65,66,67] : List Nat)) (b : Option Bool) :
    After k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k)
      ((Cursor.machine k).step (Cursor.q k i) b).1)) := by
  have limits : i ≤ 67  ∧  i ≠ 39  ∧  i ≠ 40 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega
  have notVerdict (j : Nat) (hj : j ≤ 67) (ne : i ≠ j) : Cursor.q k i ≠ Cursor.q k j := by
    intro bad; have e:=congrArg Fin.val bad
    change i%Cursor.stateCount k=j%Cursor.stateCount k at e
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega),Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at e
    omega
  have na : Cursor.q k i ≠ (Cursor.machine k).accept:=notVerdict 39 (by decide) limits.2.1
  have nr : Cursor.q k i ≠ (Cursor.machine k).reject:=notVerdict 40 (by decide) limits.2.2
  rw [UniformTM.step_of_ne (Cursor.machine k) na nr]
  change After k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k)
    (cursor_decode k (cursor_program k) (Cursor.q k i) b).1))
  exact eof_decode k (cursor_program k) i member b
private theorem after_step {k s} (h : After k s) (b : Option Bool) : After k ((CanonicalLeaf.machine k).step s b).1 := by
  rcases h with closed | ⟨i,mem,eq⟩
  · left; fromDonor "CarryWindow.Raw" "CarryWindow" "closed_step" => exact OLD k s b closed
  · subst s
    have bounds : i  ≤  307 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at mem; omega
    fromDonor "CarryReadyCompletion.Native" "CarryReadyCompletion" "canonical_row" =>
      have nativeRow:=OLD k i b (by unfold Cursor.stateCount; omega) (by omega)
    change (CanonicalLeaf.machine k).step (CQ k i) b=_ at nativeRow
    rw [nativeRow]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact eof_after k 57 (by decide) b
    · exact eof_after k 65 (by decide) b
    · exact eof_after k 66 (by decide) b
    · exact eof_after k 67 (by decide) b
    · exact route_after k true 0 (by decide) b
    · exact route_after k true 1 (by decide) b
    · exact route_after k true 2 (by decide) b
    · exact route_after k true 3 (by decide) b
    · exact route_after k false 0 (by decide) b
    · exact route_after k false 1 (by decide) b
    · exact route_after k false 2 (by decide) b
    · exact route_after k false 3 (by decide) b
private theorem after_run {k N B} (c : Config (CanonicalLeaf.machine k).stateCount N B) (h : After k c.state) (t : Nat) :
    After k ((CanonicalLeaf.machine k).run t c).state := by
  induction t with
  | zero => rw [UniformTM.run]; exact h
  | succ t ih => rw [UniformTM.run]; exact after_step ih _
private theorem canonical_prefix (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) (t : Nat)
    (prior : ∀ u, u     <     t      →      ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val     <     288+430+93*k) :
    let old:=initialConfig (IngressRepair.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    let c:=initialConfig (CanonicalLeaf.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∀ u, u     ≤     t      →      (CanonicalLeaf.machine k).run u c=VirtualLeaf.config k ((IngressRepair.machine k).run u old) := by
  intro old c
  have low (u : Nat) (hu : u     <     t) : ((IngressRepair.machine k).run u old).state.val     <     288+430+93*k := by
    rw [IngressRepair.accepted_transport k x w accepted u]; exact prior u hu
  fromDonor "VirtualLeaf.Transport" "VirtualLeaf" "entry_val" => have entryval:=OLD k
  fromDonor "VirtualLeaf.Transport" "VirtualLeaf" "transport" =>
    have a:=OLD old (t:=t) (by
      intro u hu bad
      have b:=low u hu
      rw [bad,entryval] at b; omega)
  fromDonor "CanonicalLeaf.Rows" "CanonicalLeaf" "transport" =>
    have b:=OLD (VirtualLeaf.config k old) (t:=t) (by
      intro u hu; rw [a u (by omega)]
      have bound:=low u hu
      change ((IngressRepair.machine k).run u old).state.val     <     (IngressRepair.machine k).stateCount
      change _     <     288+Cursor.stateCount k
      unfold Cursor.stateCount; omega)
  intro u hu; exact (b u hu).trans (a u hu)
private theorem below_cuts (k : Nat) (s : Fin (CanonicalLeaf.machine k).stateCount)
    (upper : s.val  <  288+430+93*k) : s  ≠  CQ k (430+93*k)   ∧   s  ≠  CQ k (613+93*k) := by
  have val (j : Nat) (hi : j  <  Cursor.stateCount k) : (CQ k j).val=288+j := by
    change 288+j%Cursor.stateCount k=288+j; rw [Nat.mod_eq_of_lt hi]
  constructor
  all_goals intro bad; have e:=congrArg Fin.val bad
  all_goals rw [val _ (by unfold Cursor.stateCount; omega)] at e
  all_goals omega
private theorem never_cuts (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) (t : Nat)
    (prior : ∀ u, u     <     t      →      ((AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val     <     288+430+93*k)
    (event : After k (VirtualLeaf.embed k (((AllArityCursor.machine k).run t
      (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state))) :
    let c:=initialConfig (CanonicalLeaf.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∀ u, ((CanonicalLeaf.machine k).run u c).state     ≠     CQ k (430+93*k)      ∧
      ((CanonicalLeaf.machine k).run u c).state     ≠     CQ k (613+93*k) := by
  intro c
  have prefixEq:=canonical_prefix k x w accepted t prior
  have eq (u : Nat) (hu : u   ≤   t) : (CanonicalLeaf.machine k).run u c=
      VirtualLeaf.config k ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))) := by
    have h:=prefixEq u hu
    rw [IngressRepair.accepted_transport k x w accepted] at h
    exact h
  have atEvent : After k ((CanonicalLeaf.machine k).run t c).state := by
    rw [eq t le_rfl]; exact event
  intro u
  by_cases early : u     <     t
  · apply below_cuts k
    rw [eq u (by omega)]
    exact prior u early
  · have later:=after_run ((CanonicalLeaf.machine k).run t c) atEvent (u-t)
    rw [←UniformTM.run_add,show t+(u-t)=u by omega] at later
    exact after_ne later
private theorem virtual_cuts (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    (pr : Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q))
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (branch : min (9+2*z+2^pr.2.n) (a+m)=a+m      ∨
      (min (9+2*z+2^pr.2.n) (a+m)     <     a+m      ∧      a+m-min (9+2*z+2^pr.2.n) (a+m)     <     Cursor.Target.W k pr.2.n)) :
    let c:=initialConfig (CanonicalLeaf.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∀ u, ((CanonicalLeaf.machine k).run u c).state     ≠     CQ k (430+93*k)      ∧
      ((CanonicalLeaf.machine k).run u c).state     ≠     CQ k (613+93*k) := by
  rcases branch with eof | ⟨phys,over⟩
  · obtain ⟨pr',parsed',_table,z',t,_hH,gamma',_price,_hp,pre,prior,_physical,_eof⟩:=AllArityWorkspace.accepted_raw k x w accepted
    have pe : pr'=pr:=Option.some.inj (parsed'.symm.trans parsed)
    subst pr'
    have ze : z'=z:=Option.some.inj (gamma'.symm.trans gamma)
    subst z'
    apply never_cuts k x w accepted t
    · intro u hu; exact (prior u hu).trans_le (by omega)
    · right; refine ⟨57,by simp,?_⟩
      have e:=congrArg Config.state pre
      simpa only [if_pos eof] using congrArg (VirtualLeaf.embed k) e
  · obtain ⟨t,prior,event⟩:=physical_event k x w accepted pr parsed z gamma phys over
    apply never_cuts k x w accepted t prior
    rcases event with eq | eq | eq
    · right; refine ⟨250,by simp,?_⟩; exact congrArg (VirtualLeaf.embed k) eq
    · right; refine ⟨304,by simp,?_⟩; exact congrArg (VirtualLeaf.embed k) eq
    · left; right; right; refine ⟨798,by decide,?_⟩; exact congrArg (VirtualLeaf.embed k) eq

end CarryReadyCompletion
