import CappedWorkspace.Kernel
import CappedWorkspace.Facts
namespace CappedWorkspace
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
private theorem suffix_bound (k N B p S z n Q F : Nat) (T : Nat → Option Bool)
    (pos : 0 < p) (physical : p < S) (paid : 0 < Q) (room : S+z+n+3+Q < F)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b) (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none)
    (marks : ∀ i, S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap : ∀ i, S+z+n+3+Q < i → i < F → T i=none) (fence : T F=some false)
    (fresh : ∀ i, F < i → i ≤ F+(S-p)+2 → T i=none)
    (fit : F+(S-p)+2 < tapeLength N B) :
    ∀ u, u < 2+(S-p)*(2*(F-p)+6) →
      ((Cursor.machine k).run u
        (⟨Cursor.q k 58,⟨p,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 98 := by
  run_tac do
    let env ← getEnv
    let names := env.constants.toList.map Prod.fst
    let keys : List String := ["Frame", "Frame.mk", "base", "keep", "hop", "count_iteration", "small_mod", "Path.append", "Path.first"]
    let mapping := keys.map fun key => ("OLD_"++key.replace "." "_",(names.find? fun name =>
      name.toString.startsWith "_private.SuffixCap.Kernel." && name.toString.endsWith (".SuffixCap."++key)).get!)
    let src := "(
  let r := S-p
  have fr : OLD_Frame T p S z n Q F r :=
    @OLD_Frame_mk T p S z n Q F r pos physical rfl paid room source eof reg sep assn right marks gap fence fresh
  obtain ⟨b,hb⟩ := source p le_rfl physical
  have same := OLD_keep (Cursor.q k 58) (Cursor.q k 64) p p T .stay
    (by simp only [Cursor.q,OLD_small_mod k 58 (by omega)]; omega)
    (P := F+r+2) (by dsimp [r]; omega) (by dsimp [r]; omega)
    (by rw [hb]; exact (SuffixCap.entry_rows k b).1) rfl
  have lift := OLD_hop (Cursor.q k 64) (Cursor.q k (OLD_base b)) p (p+1) T none .right
    (by simp only [Cursor.q,OLD_small_mod k 64 (by omega)]; omega)
    (P := F+r+2) (by dsimp [r]; omega) (by dsimp [r]; omega)
    (by rw [hb]; exact (SuffixCap.entry_rows k b).2) rfl
  have rest := OLD_count_iteration k T p S z n Q F r fr r 0 (by dsimp [r]; omega) (by omega) b (by simpa using hb)
  have zeroImage : SuffixCap.Target.image T F 0=T := by
    funext i; simp [SuffixCap.Target.image,show ¬(F+2 ≤ i ∧ i < F+0+2) by omega]
  simp only [Nat.add_zero,zeroImage] at rest
  have path := OLD_Path_append (OLD_Path_append same lift) rest
  have time : 1+1+r*(2*(F-p)+6)=2+(S-p)*(2*(F-p)+6) := rfl
  rw [time] at path
  intro u hu
  exact OLD_Path_first path fit u hu
)"
    let ast ← ofExcept (Parser.runParserCategory env `tactic src)
    let ast := ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1=stx.getId.toString) with
        | some (_,name) => mkIdent name
        | none => stx
      else stx
    evalTactic ast
private theorem prefix_bound (k : Nat) {N B : Nat} (y : Bitstring N) (T t : Nat)
    (oldhit : (Stream.rawMachine.run T (initialConfig Stream.rawMachine B y)).state.val=314)
    (newhit : ((Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k) B y)).state.val=314)
    (first : ∀ u, u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k) B y)).state.val ≠ 313 ∧
      ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k) B y)).state.val ≠ 314) :
    ∀ v, v < t → ((Cursor.rawMachine k).run v (initialConfig (Cursor.rawMachine k) B y)).state.val < 320 := by
  run_tac do
    let env ← getEnv
    let names := env.constants.toList.map Prod.fst
    let keys : List String := ["raw_prefix"]
    let mapping := keys.map fun key => ("OLD_"++key.replace "." "_",(names.find? fun name =>
      name.toString.startsWith "_private.SuffixCap.Raw." && name.toString.endsWith (".SuffixCap."++key)).get!)
    let src := "(exact OLD_raw_prefix k y T t oldhit newhit first)"
    let ast ← ofExcept (Parser.runParserCategory env `tactic src)
    let ast := ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1=stx.getId.toString) with
        | some (_,name) => mkIdent name
        | none => stx
      else stx
    evalTactic ast
/-- Literal initialConfig through live COUNTED to first actual six-bank workspace. -/
theorem raw_workspace (k : Nat) : Target.Raw k := by
  intro a m x w pr parsed tag hn
  obtain ⟨z,hz,gamma,countStage⟩ := SuffixCap.raw_counted k x w parsed tag hn
  refine ⟨z,hz,gamma,?_⟩
  intro room full fits physical
  obtain ⟨ct,hS,hct,firstCount,_,counted⟩ := countStage room full fits physical
  obtain ⟨z',_,gamma',streamStage⟩ := Stream.raw_body k x w parsed tag hn
  have same : z=z' := Option.some.inj (gamma.symm.trans gamma')
  subst z'
  obtain ⟨T,hH,price,_,finish⟩ := streamStage room full
  rw [if_pos fits] at finish
  obtain ⟨hp,old⟩ := finish
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let n := pr.2.n
  let F := FixedRawLengthFence.fencePos R
  let p := min (9+2*z+2^n) S
  let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 n) (S+z+2) n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  have physical' : p < S := physical
  have pe : p=9+2*z+2^n := Nat.min_eq_left (by dsimp [p] at physical'; omega)
  have pne : p ≠ S := Nat.ne_of_lt physical'
  simp only [Stream.Target.cursor] at old
  rw [if_neg pne] at old
  obtain ⟨u,hu,_,first,pre⟩ := Cursor.raw_first k x w T (Stream.q 58) (Or.inr rfl) ⟨p,hp⟩ (fun i => V i.val) old
  rw [show (Stream.q 58).val=58 from rfl] at pre
  obtain ⟨geo,scratch,hF,fence⟩ := Stream.raw_budget_cells x w gamma room
  obtain ⟨fresh,tailfit⟩ := Cursor.raw_tail_blank x w gamma room fits
  have geom : S+z+n+3 < F := geo
  have rowRoom : S+z+n+3+2^n < F := by dsimp [S,n,F,R] at *; omega
  have allocationF : F < tapeLength R B := hF
  have allocationTail : F+5*(S-p)+n+7 < tapeLength R B := tailfit
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma
    (FixedRawLengthFence.resource_bounds R).1 (Nat.le_of_lt room)
  have sourceFrame (i : Nat) (hi : i ≤ S+z+2) : V i=U i := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    rfl
  have installed (i : Nat) (hi : i ≤ S+z+2) : U i=
      FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,by dsimp [S,n,B,R] at *; omega⟩ := by
    dsimp only [U,Body.extend]
    rw [dif_pos (by dsimp [S,n,B,R] at *; omega)]
    dsimp only [Body.installedTape]
    rw [if_neg (by omega)]
  have source (i : Nat) (lo : p ≤ i) (hi : i < S) : ∃ b, V i=some b := by
    rw [sourceFrame i (by omega),installed i (by omega)]
    exact ⟨_,Body.raw_source_after_header x w gamma (FixedRawLengthFence.resource_bounds R).1
      (Nat.le_of_lt room) _ (by change 8+2*z+1 ≤ i; rw [pe] at lo; have ha : 9+2*z ≤ i := (Nat.le_add_right (9+2*z) (2^n)).trans lo; clear * - ha; omega) hi⟩
  have eof : V S=none := by
    rw [sourceFrame _ (by omega),installed _ (by omega)]
    simp only [FixedRawLengthFence.countdownTape]
    rw [if_neg (by dsimp [F,R,S,FixedRawLengthFence.fencePos,pairLength] at *; omega)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
  have sep : V (S+z+2)=none := by
    rw [sourceFrame _ le_rfl,installed _ le_rfl]
    exact cells.2.2.1 _ (by dsimp [S]; omega)
  have reg (i : Nat) (lo : S < i) (hi : i < S+z+2) : V i=some false := by
    rw [sourceFrame _ (by omega),installed _ (by omega)]
    exact cells.2.1 (i-S-1) (by omega) _ (by dsimp [S]; omega)
  have assn (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : ∃ b, V i=some b := by
    dsimp only [V,Stream.Target.image]; rw [if_pos (by omega)]; exact ⟨_,rfl⟩
  have right : V (S+z+n+3)=none := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    dsimp only [U,Body.extend]; rw [dif_pos hH]
    exact scratch _ le_rfl geo
  have marks (i : Nat) (lo : S+z+n+3 < i) (hi : i ≤ S+z+n+3+2^n) : V i=some true := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_pos ⟨by omega,by omega⟩]
  have gap (i : Nat) (lo : S+z+n+3+2^n < i) (hi : i < F) : V i=none := by
    have afterH : S+z+n+3 < i := lt_of_le_of_lt (Nat.le_add_right (S+z+n+3) (2^n)) lo
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by clear * - afterH; dsimp [S,n] at *; omega),if_neg (by clear * - lo; dsimp [S,n] at *; omega)]
    dsimp only [U,Body.extend]
    rw [dif_pos (by change i < tapeLength R B; omega)]
    exact scratch _ (by change S+z+n+3 ≤ i; exact Nat.le_of_lt afterH) hi
  have vf : V F=some false := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by dsimp [S,n,F,R] at *; omega),if_neg (by dsimp [S,n,F,R] at *; omega)]
    dsimp only [U,Body.extend]; rw [dif_pos hF]; exact fence
  have fit : F+(S-p)+2 < tapeLength R B := by dsimp [F,S,p,n,R,B] at *; omega
  have newScratch (i : Nat) (lo : F < i) (hi : i ≤ F+(S-p)+2) : V i=none :=
    fresh ⟨i,by change i < tapeLength R B; clear * - hi fit; omega⟩ lo
  have arenaRoom : S+z+n+3+2^n < F := by dsimp [S,n,F,R] at *; omega
  let r := S-p
  let C := SuffixCap.Target.image V F r
  have Pfit : F+5*r+n+7 < tapeLength R B := allocationTail
  have oldC (i : Nat) (hi : i ≤ F+1) : C i=V i := by
    dsimp only [C,SuffixCap.Target.image]
    rw [if_neg (by omega)]
  have cEof : C S=none := by rw [oldC _ (by omega)]; exact eof
  have cReg (i : Nat) (lo : S < i) (hi : i < S+z+2) : C i=some false := by
    rw [oldC _ (by omega)]; exact reg i lo hi
  have cSep : C (S+z+2)=none := by rw [oldC _ (by omega)]; exact sep
  have cAssn (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : C i=some false := by
    rw [oldC _ (by omega)]
    dsimp only [V,Stream.Target.image]
    rw [if_pos ⟨lo,by omega⟩,overflow_bits]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
    split_ifs <;> rfl
  have cRight : C (S+z+n+3)=none := by rw [oldC _ (by omega)]; exact right
  have cMarks (i : Nat) (lo : S+z+n+3 < i) (hi : i ≤ S+z+n+3+2^n) : C i=some true := by
    rw [oldC _ (by omega)]; exact marks i lo hi
  have cGap (i : Nat) (lo : S+z+n+3+2^n < i) (hi : i < F) : C i=none := by
    rw [oldC _ (by omega)]; exact gap i lo hi
  have cFence : C F=some false := by rw [oldC _ (by omega)]; exact vf
  have cD0 : C (F+1)=none := by
    rw [oldC _ (by omega)]
    exact fresh ⟨F+1,by change F+1 < tapeLength R B; omega⟩ (Nat.lt_succ_self F)
  have cBank0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : C i=some true := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_pos (by omega)]
  have cFresh (i : Nat) (lo : F+r+2 ≤ i) (hi : i ≤ F+5*r+n+7) : C i=none := by
    dsimp only [C,SuffixCap.Target.image]
    rw [if_neg (by omega)]
    exact fresh ⟨i,by change i < tapeLength R B; omega⟩ (by change F < i; omega)
  obtain ⟨t,ht,runSetup,beforeSetup⟩ := workspace k R B S (S+z+2) n (2^n) F r C
    (by omega) (by positivity) (by omega) cEof cReg cSep
    (by intro i lo hi; exact cAssn i lo (by omega))
    (by rw [show S+z+2+n+1=S+z+n+3 by omega]; exact cRight)
    (by intro i lo hi; exact cMarks i (by omega) (by omega))
    (by intro i lo hi; exact cGap i (by omega) hi) cFence cD0 cBank0 cFresh Pfit
  let countCost := 2+r*(2*(F-p)+6)
  have priorBound := prefix_bound k (encodePair x w) T u (by rw [old]; rfl) (by rw [pre]; rfl) first
  have countRun := SuffixCap.counted k R B p S z n (2^n) F V (by rw [pe]; positivity) physical'
    (by positivity) arenaRoom source eof reg sep assn right marks gap vf newScratch fit
  have countBound := suffix_bound k R B p S z n (2^n) F V (by rw [pe]; positivity) physical'
    (by positivity) arenaRoom source eof reg sep assn right marks gap vf newScratch fit
  have rawCount : (Cursor.rawMachine k).run (u+countCost)
      (initialConfig (Cursor.rawMachine k) B (encodePair x w))=
      FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.rReady k,⟨S,hS⟩,fun i => C i.val⟩ := by
    rw [UniformTM.run_add,pre]
    simp only [Cursor.rawMachine,FixedRawLengthFence.prefixed.seq_run_right]
    rw [countRun.1]
  have beforeCount : ∀ v, v < u+countCost →
      ((Cursor.rawMachine k).run v (initialConfig (Cursor.rawMachine k) B (encodePair x w))).state.val < 354 := by
    intro v hv
    by_cases early : v < u
    · exact (priorBound v early).trans_le (by omega)
    · have localBound := countBound (v-u) (by dsimp only [countCost,r] at hv; omega)
      rw [show v=u+(v-u) by omega,UniformTM.run_add,pre]
      simp only [Cursor.rawMachine,FixedRawLengthFence.prefixed.seq_run_right]
      exact Nat.add_lt_add_left localBound 256
  have sameTime : ct=u+countCost := by
    apply Nat.le_antisymm
    · by_contra no
      exact firstCount (u+countCost) (by omega) (congrArg Config.state rawCount)
    · by_contra no
      have lim := beforeCount ct (by omega)
      change ((Cursor.rawMachine k).run ct (initialConfig (Cursor.rawMachine k) B (encodePair x w))).state.val < 354 at lim
      rw [counted] at lim
      change 256+98 % Cursor.stateCount k < 354 at lim
      rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at lim
      omega
  refine ⟨ct+t,by change F+1 < tapeLength R B; omega,?_,?_,Pfit,?_⟩
  · have sBound : S ≤ R := by dsimp only [S,R,pairLength]; omega
    have rBound : r ≤ R := (Nat.sub_le S p).trans sBound
    have nBound : n ≤ 3*R+2 := by dsimp only [F,FixedRawLengthFence.fencePos] at geom; omega
    have c1 : n+r+1 ≤ 8*(R+1) := by omega
    have c2 : F+5*r+n+9 ≤ 18*(R+1) := by dsimp only [F,FixedRawLengthFence.fencePos]; omega
    have stagePrice : t ≤ 32768*(R+1)^2 := by
      calc
        t ≤ 128*(n+r+1)*(F+5*r+n+9) := ht
        _ ≤ 128*(8*(R+1))*(18*(R+1)) := Nat.mul_le_mul (Nat.mul_le_mul_left 128 c1) c2
        _ ≤ 32768*(R+1)^2 := by nlinarith only [Nat.zero_le ((R+1)^2)]
    change ct+t ≤ 1048576*(R+1)^3
    change ct ≤ 65536*(R+1)^2 at hct
    nlinarith only [hct,stagePrice,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
  · intro v hv equal
    have ev := congrArg Fin.val equal
    have targetVal : (FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 201)).val=457 := by
      change 256+201 % Cursor.stateCount k=457
      rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
    rw [targetVal] at ev
    by_cases early : v < ct
    · have lim := beforeCount v (by rw [← sameTime]; exact early)
      exact (Nat.ne_of_lt (lim.trans (by decide : 354 < 457))) ev
    · have localBound := beforeSetup (v-ct) (by omega)
      rw [show v=ct+(v-ct) by omega,UniformTM.run_add,counted] at ev
      simp only [Cursor.rawMachine,FixedRawLengthFence.prefixed.seq_run_right] at ev
      have bad : ((Cursor.machine k).run (v-ct)
          (⟨Cursor.rReady k,⟨S,hS⟩,fun i => C i.val⟩ : Config (Cursor.machine k).stateCount R B)).state.val=201 := Nat.add_left_cancel ev
      exact (Nat.ne_of_lt localBound) bad
  · rw [UniformTM.run_add,counted]
    simp only [Cursor.rawMachine,FixedRawLengthFence.prefixed.seq_run_right]
    rw [runSetup]
/-- Accepted specialization, same parsed pr and original dependent allocation. -/
theorem raw_accepted_workspace (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (hn : 3 ≤ pr.2.n) :
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (min (9+2*z+2^pr.2.n) (a+m) < a+m →
        ∃ (t : Nat) (hD : FixedRawLengthFence.fencePos (pairLength a m)+1 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ Target.deadline (pairLength a m) ∧
          (∀ u, u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 201)) ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let T := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
          FixedRawLengthFence.fencePos (pairLength a m)+5*((a+m)-min (9+2*z+2^pr.2.n) (a+m))+pr.2.n+7 <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 201,⟨FixedRawLengthFence.fencePos (pairLength a m)+1,hD⟩,fun i =>
                Target.image (SuffixCap.Target.image T (FixedRawLengthFence.fencePos (pairLength a m))
                  ((a+m)-min (9+2*z+2^pr.2.n) (a+m))) (a+m+z+2) pr.2.n
                  (FixedRawLengthFence.fencePos (pairLength a m))
                  ((a+m)-min (9+2*z+2^pr.2.n) (a+m)) i.val⟩) := by
  obtain ⟨pr',parsed',table,_⟩ := AcceptedBody.exact k x w accepted
  have same : pr'=pr := Option.some.inj (parsed'.symm.trans parsed)
  subst pr'
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
  obtain ⟨z,hz,gamma,_⟩ := SuffixCap.raw_accepted_counted k x w accepted parsed hn
  obtain ⟨z',_,gamma',stage⟩ := raw_workspace k x w parsed tag hn
  have sameGamma : z'=z := Option.some.inj (gamma'.symm.trans gamma)
  subst z'
  have full := GammaSupport.exact k x w parsed semantic hn z gamma
  have small : pr.2.n ≤ a+m := by
    have h := Nat.lt_two_pow_self (n := pr.2.n)
    change 2^pr.2.n ≤ a+m at table
    omega
  exact ⟨z,hz,gamma,stage (AcceptedBody.strict_capacity x w gamma small) full
    (Stream.accepted_rows_fit k x w accepted parsed gamma)⟩
end CappedWorkspace
