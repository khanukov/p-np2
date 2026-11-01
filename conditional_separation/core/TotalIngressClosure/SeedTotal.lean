import TotalIngressClosure.LengthTotal
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
open IngressAllocation (Footprint)
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let specs := [("TotalIngressClosure.LengthTotal","TotalIngressClosure","physical_length_heads","rawLength"),
    ("PowerDriver.Raw","PowerDriver","prepared_seed","preparedSeed"),
    ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells"),
    ("TotalIngressClosure.Header","TotalIngressClosure","table_budget_width","tableWidth")]
  let fields := ["arena","source","eof","reg","sep","assn","right","marks","gap","fence"]
  let specs := specs ++ fields.map fun f => ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells."++f,"cell_"++f)
  for (mod,ns,key,aliasName) in specs do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique exact workspace raw interface {mod}/{key}: {found.map Prod.fst}"
private theorem seed_empty (L n F r : Nat) (C : Nat → Option Bool)
    (room : L+n+1 < F) (rp : 0 < r) :
    RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image C L n F r) L n F r (F+2*r+n+5)=some false:=by
  have minle:=Nat.min_le_right (bitLength n) r
  dsimp only [RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
private theorem short_seed_bound (R n r L : Nat) (big : 12 ≤ R) (nr : n ≤ R) (rr : r ≤ R)
    (ll : L ≤ 2*R+2) : L+16*(3*R+2+5*r+n+8) ≤ 12*(R+1)^2:=by
  have square:=Nat.mul_le_mul_left R big
  nlinarith only [square,big,nr,rr,ll]
set_option maxRecDepth 4000 in
private theorem physical_seed_heads (k : Nat) {a m n0 consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n0,consumed))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical:z=0 ∨ 9+z < a+m) (cap:n0 < FixedRawLengthFence.capacity a m z)
    (rows:2^n0 ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n0+3)-1)
    (physical : min (9+2*z+2^n0) (a+m) < a+m) :
    let S:=a+m;let n:=n0;let L:=S+z+2;let F:=3*pairLength a m+2
    let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    ∃ (t : Nat) (hF : (if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3) < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      t ≤ 8388608*(pairLength a m+1)^3 ∧
      (AllArityCursor.machine k).run t
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k) ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
          ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,hF⟩,fun i=>(if bitLength n ≤ r then Z else Y) i.val⟩ ∧
      Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) ∧
      (∀ u,u ≤ t → ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val ≤ 617) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=n0;let L:=S+z+2;let F:=3*R+2
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let C:=SuffixCap.Target.image V F r
  let X:=CappedWorkspace.Target.image C L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  obtain ⟨t,ht,lengthPrice,atLength,lengthHeads,lengthControl⟩:=rawLength k x w header tag gamma firstPhysical cap rows physical
  change (if bitLength n ≤ r then L else F+r+n+3) < tapeLength R B at ht
  change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
    ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
      ⟨if bitLength n ≤ r then L else F+r+n+3,ht⟩,fun i=>Y i.val⟩ at atLength
  by_cases fits : bitLength n ≤ r
  · obtain ⟨cf,_short,fresh⟩:=actualCells x w gamma cap rows
    obtain ⟨_legacy,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
    change F+5*r+n+7 < tapeLength R B at fit
    change ∀ i : Fin (tapeLength R B),F < i.val → V i.val=none at fresh
    have arena : L+n+1+2^n < F:=by have h:=cell_arena cf;change S+z+n+3+2^n < F at h;dsimp only [L];omega
    have rp : 0 < r:=by change p < S at physical;dsimp only [r];omega
    have frame:=preparedSeed L n (2^n) F r V rp fits (by positivity) arena
      (cell_sep cf) (by rw [show L+n+1=S+z+n+3 by dsimp only [L];omega];exact cell_right cf)
      (by
        intro i lo hi
        exact cell_marks cf i (by change S+z+n+3 < i;dsimp only [L] at lo;omega)
          (by change i ≤ S+z+n+3+2^n;dsimp only [L] at hi;omega))
      (by intro i lo hi;exact cell_gap cf i (by change S+z+n+3+2^n < i;dsimp only [L] at lo;omega) hi)
      (cell_fence cf) (by intro i lo hi;exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
    rcases frame with ⟨_paid,_room,zsep,zright,zmarks,zgap,zfence,zds,zbanks,_assignment⟩
    have oldY (i : Nat) (hi : i ≤ F+2*r+n+4) : Y i=Z i:=by
      dsimp only [Z,AllArityBitLength.Target.seedImage];rw [if_neg (by omega)]
    have occ (j : Nat) (hj : j < 3) : ∀ i,
        (match j with | 0=>F+1 | 1=>F+r+2 | _=>F+r+n+3) < i →
        i < (match j with | 0=>F+r+2 | 1=>F+r+n+3 | _=>F+2*r+n+4) → ∃ b,Y i=some b:=by
      intro i lo hi
      interval_cases j
      all_goals rw [oldY i (by dsimp only at hi;omega)]
      · exact ⟨_,zbanks 0 (by decide) i lo hi⟩
      · exact ⟨_,zbanks 1 (by decide) i lo hi⟩
      · exact ⟨_,zbanks 2 (by decide) i lo hi⟩
    have yds (i : Nat) (hi : i=F+1 ∨ i=F+r+2 ∨ i=F+r+n+3 ∨ i=F+2*r+n+4) : Y i=none:=by
      rw [oldY i (by omega)]
      rcases hi with rfl|rfl|rfl|rfl
      · exact zds 0 (by decide)
      · exact zds 1 (by decide)
      · exact zds 2 (by decide)
      · exact zds 3 (by decide)
    obtain ⟨s,price,seedRun,seedFirst⟩:=AllArityBitLength.seed k R B L n (2^n) F r Y rp arena
      (by rw [oldY _ (by omega)];exact zsep)
      (by intro i lo hi;dsimp only [Y,RuntimeBitLength.Target.fullImage];rw [if_pos ⟨lo,hi⟩];exact ⟨_,rfl⟩)
      (by rw [oldY _ (by omega)];exact zright)
      (by
        intro i lo hi
        rw [oldY i (by omega)]
        by_cases marked : i ≤ L+n+1+2^n
        · exact Or.inr (zmarks i lo marked)
        · exact Or.inl (zgap i (by omega) hi))
      (by rw [oldY _ (by omega)];exact zfence)
      (yds _ (Or.inl rfl)) (occ 0 (by decide)) (yds _ (Or.inr (Or.inl rfl)))
      (occ 1 (by decide)) (yds _ (Or.inr (Or.inr (Or.inl rfl))))
      (occ 2 (by decide)) (yds _ (Or.inr (Or.inr (Or.inr rfl))))
      (seed_empty L n F r C (by omega) rp) fit
    have hL : L < tapeLength R B:=by simpa only [if_pos fits] using ht
    have atStart : (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k 308,⟨L,hL⟩,fun i=>Y i.val⟩:=by simpa only [if_pos fits] using atLength
    have replay (s : Nat) (config : Config (Cursor.machine k).stateCount R B) :
        (AllArityCursor.machine k).run s (SmallIngress.producer.seqEmbedRight (Cursor.machine k) config)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run s config):=by
      change (SmallIngress.producer.seq (Cursor.machine k)).run s _=_
      rw [UniformTM.seq_run_right]
    have endRun : (AllArityCursor.machine k).run (t+s) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k 329,⟨F+2*r+n+4,by change F+2*r+n+4 < tapeLength R B;omega⟩,fun i=>Z i.val⟩:=by
      rw [UniformTM.run_add,atStart,replay,seedRun]
    have pair : S+1 ≤ R:=by dsimp only [S,R,pairLength];omega
    have nr : n ≤ R:=tableWidth R S z n (by dsimp only [R,pairLength];omega) (by
      change S+z+n+3+2^n < F
      dsimp only [L] at arena
      omega)
    have rr : r ≤ R:=(Nat.sub_le _ _).trans (by omega)
    have pe : p=9+2*z+2^n:=Nat.min_eq_left (by change min (9+2*z+2^n) S < S at physical;omega)
    have power : 0 < 2^n:=by positivity
    have big : 12 ≤ R:=by change p < S at physical;rw [pe] at physical;omega
    have gammaBound:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    have ll : L ≤ 2*R+2:=by change 8+z < S at gammaBound;dsimp only [L];omega
    have tailBound : L+16*(F+5*r+n+8) ≤ 12*(R+1)^2:=short_seed_bound R n r L big nr rr ll
    have fitEnd : (if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3) < tapeLength R B:=by split <;> omega
    have total:t+s ≤ 8388608*(R+1)^3:=by
      have tp:t ≤ 4194304*(R+1)^3:=lengthPrice
      have sp:s ≤ 16*(F+5*r+n+8):=price
      dsimp only [F] at sp
      nlinarith only [tp,sp,nr,rr,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
    refine ⟨t+s,fitEnd,total,?_,?_,?_⟩
    · change (AllArityCursor.machine k).run (t+s) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
          ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,fitEnd⟩,
          fun i=>(if bitLength n ≤ r then Z else Y) i.val⟩
      simpa only [if_pos fits] using endRun
    · intro u hu
      by_cases early : u ≤ t
      · exact lengthHeads u early
      · rw [show u=t+(u-t) by omega,UniformTM.run_add,atStart,replay]
        have speed:=(Cursor.machine k).run_head_le (steps:=u-t)
          (⟨Cursor.q k 308,⟨L,hL⟩,fun i=>Y i.val⟩ : Config (Cursor.machine k).stateCount R B)
        exact speed.trans (by change L+(u-t) ≤ 12*(R+1)^2;omega)
    · intro u hu
      by_cases early : u ≤ t
      · exact lengthControl u early
      · by_cases last : u < t+s
        · rw [show u=t+(u-t) by omega,UniformTM.run_add,atStart,replay]
          exact (Nat.add_lt_add_left (seedFirst (u-t) (by omega)) 288).le
        · have eq : u=t+s:=by omega
          rw [eq,endRun]
          change 288+329%Cursor.stateCount k ≤ 617
          rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]
  · have fitEnd : (if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3) < tapeLength R B:=by
      simpa only [if_neg fits] using ht
    have total:t ≤ 8388608*(R+1)^3:=by
      have tp:t ≤ 4194304*(R+1)^3:=lengthPrice
      omega
    refine ⟨t,fitEnd,total,?_,lengthHeads,lengthControl⟩
    change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
        ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,fitEnd⟩,
        fun i=>(if bitLength n ≤ r then Z else Y) i.val⟩
    simpa only [if_neg fits] using atLength
end TotalIngressClosure
