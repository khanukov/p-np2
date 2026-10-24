import SuffixCap.Kernel
namespace SuffixCap
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open Lean Elab Tactic
/-- Reuse the immutable whole-prefix transport, retaining its stronger state bound. -/
private theorem raw_prefix (k : Nat) {N B : Nat} (y : Bitstring N) (T t : Nat)
    (oldhit : (Stream.rawMachine.run T (initialConfig Stream.rawMachine B y)).state.val=314)
    (newhit : ((Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k) B y)).state.val=314)
    (first : ∀ u, u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k) B y)).state.val ≠ 313 ∧
      ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k) B y)).state.val ≠ 314) :
    ∀ v, v < t → ((Cursor.rawMachine k).run v (initialConfig (Cursor.rawMachine k) B y)).state.val < 320 := by
  run_tac do
    let names := (← getEnv).constants.toList.map Prod.fst
    let get (s : String) := Lean.mkIdent ((names.find? fun n =>
      n.toString.startsWith "_private.Cursor.Proof." && n.toString.endsWith (".Cursor."++s)).get!)
    let er := get "er"; let exits := get "exits"; let inert := get "old_inert"
    let row := get "raw_row"; let ini := get "er_initial"; let value := get "er_val"
    let kv := mkIdent `k
    let Bv := mkIdent `B
    let yv := mkIdent `y
    let Tv := mkIdent `T
    let tv := mkIdent `t
    let oldhitv := mkIdent `oldhit
    let newhitv := mkIdent `newhit
    let firstv := mkIdent `first
    evalTactic (← `(tactic| (
      have hit : $exits:ident (Stream.rawMachine.run $Tv:ident (initialConfig Stream.rawMachine $Bv:ident $yv:ident)).state := Or.inr $oldhitv:ident
      obtain ⟨u,_,oldfirst,_,eq,path⟩ := Cursor.Transport.first_changed_rows
        Stream.rawMachine (Cursor.rawMachine $kv:ident) ($er:ident $kv:ident) $exits:ident
        (fun c h => $inert:ident c h) ($row:ident $kv:ident) (initialConfig Stream.rawMachine $Bv:ident $yv:ident) $Tv:ident hit
      rw [$ini:ident] at eq path
      have finalVal : ((Cursor.rawMachine $kv:ident).run u (initialConfig (Cursor.rawMachine $kv:ident) $Bv:ident $yv:ident)).state.val=314 := by
        rw [eq]; simpa only [$value:ident] using $oldhitv:ident
      have same : $tv:ident=u := by
        apply Nat.le_antisymm
        · by_contra h; exact ($firstv:ident u (by omega)).2 finalVal
        · by_contra h
          have mapped := path $tv:ident (by omega)
          have ev : (Stream.rawMachine.run $tv:ident (initialConfig Stream.rawMachine $Bv:ident $yv:ident)).state.val=314 := by
            have ev := congrArg (fun c => c.state.val) mapped
            simpa only [$value:ident,$newhitv:ident] using ev.symm
          exact oldfirst $tv:ident (by omega) (Or.inr ev)
      intro v hv
      rw [path v (by omega)]
      simpa only [$value:ident] using (Stream.rawMachine.run v (initialConfig Stream.rawMachine $Bv:ident $yv:ident)).state.isLt)))

/-- Literal initialConfig to strict first COUNTED, on Cursor.rawMachine without new runtime rows. -/
theorem raw_counted (k : Nat) : Target.Raw k := by
  intro a m x w pr parsed tag hn
  obtain ⟨z,hz,gamma,stage⟩ := Stream.raw_body k x w parsed tag hn
  refine ⟨z,hz,gamma,?_⟩
  intro room full fits physical
  obtain ⟨T,hH,price,_,finish⟩ := stage room full
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
  obtain ⟨t,ht,_,first,pre⟩ := Cursor.raw_first k x w T (Stream.q 58) (Or.inr rfl) ⟨p,hp⟩ (fun i => V i.val) old
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
  have kernel := counted k R B p S z n (2^n) F V (by rw [pe]; positivity) physical'
    (by positivity) arenaRoom source eof reg sep assn right marks gap vf newScratch fit
  let cost := 2+(S-p)*(2*(F-p)+6)
  refine ⟨t+cost,by change S < tapeLength R B; clear * - geom allocationF; omega,?_,?_,fit,?_⟩
  · have small : S-p ≤ R := (Nat.sub_le S p).trans (by dsimp [S,R,pairLength]; omega)
    have costBound : cost ≤ 16*(R+1)^2 := by
      calc
        cost  ≤  2+R*(2*F+6) := Nat.add_le_add_left (Nat.mul_le_mul small (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.sub_le F p)) 6)) 2
        _  ≤  16*(R+1)^2 := by dsimp [F,FixedRawLengthFence.fencePos]; nlinarith
    change t+cost ≤ 65536*(R+1)^2
    nlinarith only [ht,price,costBound,Nat.zero_le ((R+1)^2)]
  · have boundPrefix := raw_prefix k (encodePair x w) T t
      (by rw [old]; rfl) (by rw [pre]; rfl) first
    intro u hu eq
    by_cases before : u < t
    · have lim := boundPrefix u before
      rw [eq] at lim
      change 256+98 % Cursor.stateCount k < 320 at lim
      rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at lim
      omega
    · have avoid := kernel.2 (u-t) (by dsimp [cost] at hu; omega)
      apply avoid
      have ev := congrArg Fin.val eq
      rw [show u=t+(u-t) by omega,UniformTM.run_add,pre] at ev
      simp only [Cursor.rawMachine,FixedRawLengthFence.prefixed.seq_run_right] at ev
      apply Fin.ext
      change 256+_=256+_ at ev
      exact Nat.add_left_cancel ev
  · rw [UniformTM.run_add,pre]
    change (FixedRawLengthFence.prefixed.seq (Cursor.machine k)).run cost
      (FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k) ⟨Cursor.q k 58,⟨p,hp⟩,fun i => V i.val⟩)=_
    rw [FixedRawLengthFence.prefixed.seq_run_right,kernel.1]
/-- Accepted specialization uses the same parsed parameter and discharges physical guards only. -/
theorem raw_accepted_counted (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (hn : 3 ≤ pr.2.n) :
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (min (9+2*z+2^pr.2.n) (a+m) < a+m →
        ∃ (t : Nat) (hS : a+m < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ Target.deadline (pairLength a m) ∧
          (∀ u, u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.rReady k)) ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let T := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
          FixedRawLengthFence.fencePos (pairLength a m)+((a+m)-min (9+2*z+2^pr.2.n) (a+m))+2 <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
            FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.rReady k,⟨a+m,hS⟩,fun i => Target.image T (FixedRawLengthFence.fencePos (pairLength a m))
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
  obtain ⟨z,hz,gamma,stage⟩ := raw_counted k x w parsed tag hn
  have full := GammaSupport.exact k x w parsed semantic hn z gamma
  have small : pr.2.n ≤ a+m := by
    have h := Nat.lt_two_pow_self (n := pr.2.n)
    change 2^pr.2.n ≤ a+m at table
    omega
  exact ⟨z,hz,gamma,stage (AcceptedBody.strict_capacity x w gamma small) full
    (Stream.accepted_rows_fit k x w accepted parsed gamma)⟩
end SuffixCap
