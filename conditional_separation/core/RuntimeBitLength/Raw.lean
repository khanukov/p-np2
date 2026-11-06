import RuntimeBitLength.Kernel
namespace RuntimeBitLength
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
private theorem clock_bound (R L n r t0 t : Nat) (room : L+n+1 < 3*R+2)
    (hr : r ≤ R) (priorBound : t0 ≤ 1048576*(R+1)^3)
    (phase : t ≤ 128*(n+1)*(3*R+2+5*r+n+8)) : t0+t ≤ 2097152*(R+1)^3 := by
  have hn : n+1 ≤ 3*(R+1) := by omega
  have hp : 3*R+2+5*r+n+8 ≤ 12*(R+1) := by omega
  have mul := Nat.mul_le_mul (Nat.mul_le_mul_left 128 hn) hp
  have sq : t ≤ 4608*(R+1)^2 := by nlinarith only [phase,mul]
  have grow : (R+1)^2 ≤ (R+1)^3 := by nlinarith only [Nat.zero_le (R*(R+1)^2)]
  omega
/-- Original raw initialConfig to physically computed floor(n/2), after first q201. -/
theorem raw_half (k : Nat) : Target.Raw k := by
  intro a m x w pr parsed tag hn
  obtain ⟨z,hz,gamma,stage⟩ := CappedWorkspace.raw_workspace k x w parsed tag hn
  refine ⟨z,hz,gamma,?_⟩
  intro room full fits physical
  obtain ⟨t0,hD,price,first,Pfit,atWorkspace⟩ := stage room full fits physical
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let L := S+z+2
  let n := pr.2.n
  let F := FixedRawLengthFence.fencePos R
  let r := S-min (9+2*z+2^n) S
  let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 n) L n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let C := SuffixCap.Target.image V F r
  let X := CappedWorkspace.Target.image C L n F r
  have lEq : L=S+z+2 := rfl
  have sEq : S=a+m := rfl
  have nEq : n=pr.2.n := rfl
  have fEq : F=FixedRawLengthFence.fencePos (pairLength a m) := rfl
  obtain ⟨geo,scratch,hF,fence⟩ := Stream.raw_budget_cells x w gamma room
  obtain ⟨fresh,_⟩ := Cursor.raw_tail_blank x w gamma room fits
  have rowRoom : L+n+1+2^n < F := by dsimp [L,S,n,F,R] at *; omega
  have hr : 0 < r := by dsimp [r,S,n]; omega
  have fit : F+5*r+n+7 < tapeLength R B := Pfit
  have oldX (i : Nat) (ha : i ≤ L ∨ L+n+1 ≤ i) (hi : i ≤ F+1) : X i=V i := by
    dsimp only [X,C,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  have vInstalled (i : Nat) (hi : i ≤ L) : V i=
      FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,by change i < tapeLength R B; omega⟩ := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    change U i=_
    dsimp only [U,Body.extend]
    rw [dif_pos (by change i < tapeLength R B; omega)]
    dsimp only [Body.installedTape]; rw [if_neg (by omega)]
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma
    (FixedRawLengthFence.resource_bounds R).1 (Nat.le_of_lt room)
  have sep : X L=none := by
    rw [oldX L (by omega) (by omega),vInstalled L le_rfl]
    exact cells.2.2.1 _ (by dsimp [L,S]; omega)
  have assn (i : Nat) (lo : L < i) (hi : i < L+n+1) : X i=some true := by
    dsimp only [X,CappedWorkspace.Target.image]; rw [if_pos ⟨lo,hi⟩]
  have right : X (L+n+1)=none := by
    rw [oldX _ (by omega) (by omega)]
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    change U (L+n+1)=none
    dsimp only [U,Body.extend]; rw [dif_pos (by change L+n+1 < tapeLength R B; omega)]
    exact scratch _ (by dsimp [L,S,n]; omega) (by change L+n+1 < F; omega)
  have marks (i : Nat) (lo : L+n+1 < i) (hi : i ≤ L+n+1+2^n) : X i=some true := by
    rw [oldX i (by omega) (by omega)]
    dsimp only [V,Stream.Target.image]; rw [if_neg (by omega),if_pos (by omega)]
  have gap (i : Nat) (lo : L+n+1+2^n < i) (hi : i < F) : X i=none := by
    have above : L+n+1 < i := lt_of_le_of_lt (Nat.le_add_right (L+n+1) (2^n)) lo
    rw [oldX i (Or.inr (Nat.le_of_lt above)) (by omega)]
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by clear * - above lEq; omega),if_neg (by clear * - lo lEq; omega)]
    change U i=none
    dsimp only [U,Body.extend]; rw [dif_pos (by change i < tapeLength R B; omega)]
    have lower : a+m+z+pr.2.n+3 ≤ i := by
      calc
        a+m+z+pr.2.n+3 = L+n+1 := by dsimp only [L,S,n]; omega
        _ ≤ i := Nat.le_of_lt above
    exact scratch ⟨i,by change i < tapeLength R B; omega⟩ lower hi
  have xf : X F=some false := by
    rw [oldX F (by omega) (by omega)]
    dsimp only [V,Stream.Target.image]; rw [if_neg (by omega),if_neg (by omega)]
    change U F=some false
    dsimp only [U,Body.extend]; rw [dif_pos hF]; exact fence
  have vFresh (i : Nat) (lo : F < i) (hi : i ≤ F+5*r+n+7) : V i=none :=
    fresh ⟨i,by change i < tapeLength R B; omega⟩ lo
  have d0 : X (F+1)=none := by rw [oldX _ (by omega) le_rfl]; exact vFresh _ (by omega) (by omega)
  have b0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : X i=some true := by
    dsimp only [X,C,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  have d1 : X (F+r+2)=none := by
    dsimp only [X,C,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]; exact vFresh _ (by omega) (by omega)
  have b1 (i : Nat) (lo : F+r+2 < i) (hi : i < F+r+n+3) : X i=some false := by
    dsimp only [X,CappedWorkspace.Target.image]; rw [if_neg (by omega),if_pos (by omega)]
  have d2 : X (F+r+n+3)=none := by
    dsimp only [X,C,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]; exact vFresh _ (by omega) (by omega)
  have b2 : X (F+r+n+4)=some false := by
    dsimp only [X,CappedWorkspace.Target.image]; rw [if_neg (by omega),if_pos (by omega)]
  obtain ⟨t,ht,runHalf,early⟩ := halve k R B L n (2^n) F r X (by dsimp [n]; omega) hr
    (by positivity) rowRoom sep assn right marks gap xf d0 b0 d1 b1 d2 b2 fit
  have headFit : F+r+2 < tapeLength R B := by omega
  refine ⟨t0,t0+t,headFit,?_,by omega,?_,first,?_,fit,?_⟩
  · apply clock_bound R L n r t0 t (by change L+n+1 < F; omega) ?_ price ht
    have h := Nat.sub_le S (min (9+2*z+2^n) S)
    dsimp [S,R,pairLength] at *; omega
  · rw [atWorkspace]; rfl
  · intro u lo hi eq
    have e := early (u-t0) (by omega)
    have ev := congrArg Fin.val eq
    have targetVal : (FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 254)).val=510 := by
      change 256+254 % Cursor.stateCount k=510
      rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
    rw [targetVal] at ev
    rw [show u=t0+(u-t0) by omega,UniformTM.run_add,atWorkspace] at ev
    simp only [Cursor.rawMachine,FixedRawLengthFence.prefixed.seq_run_right] at ev
    have bad : ((Cursor.machine k).run (u-t0)
        (⟨Cursor.q k 201,⟨F+1,hD⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount R B)).state.val=254 := Nat.add_left_cancel ev
    exact (Nat.ne_of_lt e) bad
  · rw [UniformTM.run_add,atWorkspace]
    simp only [Cursor.rawMachine,FixedRawLengthFence.prefixed.seq_run_right]
    rw [runHalf]
/-- Exact original relation specialization, with the same dependent parsed pr. -/
theorem raw_accepted_half (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (hn : 3 ≤ pr.2.n) :
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (min (9+2*z+2^pr.2.n) (a+m) < a+m →
        ∃ (t0 t : Nat) (h : FixedRawLengthFence.fencePos (pairLength a m)+
            ((a+m)-min (9+2*z+2^pr.2.n) (a+m))+2 <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ 2097152*(pairLength a m+1)^3 ∧ t0 ≤ t ∧
          ((Cursor.rawMachine k).run t0 (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state =
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 201) ∧
          (∀ u, u < t0 → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 201)) ∧
          (∀ u, t0 ≤ u → u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 254)) ∧
          let S := a+m
          let n := pr.2.n
          let F := FixedRawLengthFence.fencePos (pairLength a m)
          let r := S-min (9+2*z+2^n) S
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (S+z+2) n)
          let T := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
          let X := CappedWorkspace.Target.image (SuffixCap.Target.image T F r) (S+z+2) n F r
          F+5*r+n+7 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 254,⟨F+r+2,h⟩,fun i => Target.image X (S+z+2) n F r i.val⟩) := by
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
  obtain ⟨z,hz,gamma,_⟩ := CappedWorkspace.raw_accepted_workspace k x w accepted parsed hn
  obtain ⟨z',_,gamma',stage⟩ := raw_half k x w parsed tag hn
  have sameGamma : z'=z := Option.some.inj (gamma'.symm.trans gamma)
  subst z'
  have full := GammaSupport.exact k x w parsed semantic hn z gamma
  have small : pr.2.n ≤ a+m := by
    have h := Nat.lt_two_pow_self (n := pr.2.n)
    change 2^pr.2.n ≤ a+m at table
    omega
  exact ⟨z,hz,gamma,stage (AcceptedBody.strict_capacity x w gamma small) full
    (Stream.accepted_rows_fit k x w accepted parsed gamma)⟩
end RuntimeBitLength
