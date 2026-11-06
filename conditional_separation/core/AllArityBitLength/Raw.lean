import Complexity.PrivateInterfaceLookupResolvedRuntime
import AllArityBitLength.Kernel
import AllArityBitLength.Control
import AllArityWorkspace.Layout
namespace AllArityBitLength
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private theorem right_run {k N B : Nat} (t : Nat) (d : Config (Cursor.machine k).stateCount N B) :
    (AllArityCursor.machine k).run t (SmallIngress.producer.seqEmbedRight (Cursor.machine k) d)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run t d) := by
  change (SmallIngress.producer.seq (Cursor.machine k)).run t _=_
  rw [UniformTM.seq_run_right]
private theorem clock (R n r ct b s : Nat) (hn : n    ≤    R) (hr : r    ≤    R)
    (hc : ct    ≤    1048576*(R+1)^3)
    (hb : b    ≤    4096*(n+r+1)^2*(3*R+2+5*r+n+8))
    (hs : s    ≤    16*(3*R+2+5*r+n+8)) : ct+b+s    ≤    67108864*(R+1)^4 := by
  have c1 : n+r+1    ≤    8*(R+1) := by omega
  have c2 : 3*R+2+5*r+n+8    ≤    18*(R+1) := by omega
  have pm := Nat.mul_le_mul (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left c1 2)) c2
  have qm := Nat.mul_le_mul_left 16 c2
  nlinarith only [hc,hb,hs,pm,qm,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3),Nat.zero_le (R^4)]
private theorem overflow_address (k n z S r : Nat) (hn : 0 < n)
    (physical : min (9+2*z+2^n) S < S) (rem : r=S-min (9+2*z+2^n) S)
    (overflow : r < bitLength n) : S < Cursor.Target.M k n z := by
  have base : 9+2*z+2^n < S := by omega
  rw [Nat.min_eq_left (Nat.le_of_lt base)] at rem
  have pos : 0 < n^k := Nat.pow_pos hn
  have mul := Nat.mul_le_mul_left (bitLength n+4) (show 1    ≤    n^k+k by omega)
  have total : S=9+2*z+2^n+r := by omega
  dsimp only [Cursor.Target.M,Cursor.Target.W]
  nlinarith only [total,overflow,mul]
private def BodyContract (k N B L n Q F r : Nat) (X : Nat → Option Bool) : Prop :=
  0 < r → 0 < Q → ∀ (room : L+n+1+Q < F),
  X L=none → (∀ i, L < i → i < L+n+1 → X i=some true) → X (L+n+1)=none →
  (∀ i, L+n+1 < i → i     ≤     L+n+1+Q → X i=some true) →
  (∀ i, L+n+1+Q < i → i < F → X i=none) → X F=some false → X (F+1)=none →
  (∀ i, F+1 < i → i < F+r+2 → X i=some true) → X (F+r+2)=none →
  (∀ i, F+r+2 < i → i < F+r+n+3 → X i=some false) → X (F+r+n+3)=none →
  (∀ i, F+r+n+3 < i → i < F+2*r+n+4 → X i=some false) → X (F+2*r+n+4)=none →
  ∀ (fit : F+5*r+n+7 < tapeLength N B),
  ∃ (t : Nat) (h : (if bitLength n     ≤     r then L else F+r+n+3) < tapeLength N B),
    t     ≤     4096*(n+r+1)^2*(F+5*r+n+8) ∧
    (∀ u, u < t → ((Cursor.machine k).run u
      (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 329) ∧
    (Cursor.machine k).run t (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.q k (if bitLength n     ≤     r then 308 else if (r+1)%2=1 then 250 else 304),
        ⟨if bitLength n     ≤     r then L else F+r+n+3,h⟩,
        fun i => RuntimeBitLength.Target.fullImage X L n F r i.val⟩
private theorem body (k N B L n Q F r : Nat) (X : Nat → Option Bool) : BodyContract k N B L n Q F r X := by
  intro hr paid room sep assn right marks gap fence d0 b0 d1 b1 d2 b2 d3 fit
  let C : Config (Cursor.machine k).stateCount N B := ⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i => X i.val⟩
  by_cases hn : 0 < n
  · obtain ⟨t,h,price,first,done⟩ := BitLengthDriver.prepared k N B L n Q F r X hn hr paid room sep assn right marks gap fence d0 b0 d1 b1 d2 b2 d3 fit
    refine ⟨t,h,price,?_,done⟩
    apply control_before C (Or.inr ⟨rfl,rfl⟩) (Or.inr (by change 201    ≤    201 ∧ 201    ≤    308 ∧ (201    ≤    250 ∨ 254    ≤    201) ∧ (201    ≤    304 ∨ 308    ≤    201); omega))
    intro u hu
    have guard (s : Nat) (hs : s∈[308,250,304]) : ((Cursor.machine k).run u C).state.val    ≠    s := by
      intro eq; apply first u hu s hs; apply Fin.ext
      have smem : s=308 ∨ s=250 ∨ s=304 := by simpa using hs
      have sm : s % Cursor.stateCount k=s := Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
      exact eq.trans sm.symm
    exact ⟨guard 308 (by simp),fun _ => ⟨guard 250 (by simp),guard 304 (by simp)⟩⟩
  · have zero : n=0 := by omega
    subst n
    fromDonor "RuntimeBitLength.Kernel" "RuntimeBitLength" "Frame.mk" =>
      have hf := OLD (X:=X) (L:=L) (n:=0) (Q:=Q) (F:=F) (r:=r) paid room sep assn right marks gap fence d0 b0 d1 b1 d2 (b2 _ (by omega) (by omega))
    fromDonor "RuntimeBitLength.Kernel" "RuntimeBitLength" "entry" =>
      obtain ⟨a,_exact,ha,entry⟩ := OLD k L 0 Q F r X hf
    have enter : (Cursor.machine k).run a C=
        (⟨Cursor.q k 209,⟨L,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B) := by
      fromDonor "RuntimeBitLength.Kernel" "RuntimeBitLength" "Path.execute" => exact OLD entry fit
    have prior : ∀ u, u < a → ((Cursor.machine k).run u C).state.val < 254 := by
      fromDonor "RuntimeBitLength.Kernel" "RuntimeBitLength" "Path.first" => exact OLD entry fit
    fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "Frame.mk" =>
      have df := OLD (X:=X) (L:=L) (n:=0) (Q:=Q) (F:=F) (r:=r) paid room sep assn right marks gap fence d0 b0 d1 b1 d2 b2 d3
    fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "loop" =>
      obtain ⟨b,hb,path⟩ := OLD k L 0 Q F r X df 0 0 true (by omega) (by omega) (by simp) (by simp) rfl
    fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "initial_image" =>
      have initial := OLD df
    have finish : (Cursor.machine k).run b
        (⟨Cursor.q k 209,⟨L,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)=
        ⟨Cursor.q k 308,⟨L,by omega⟩,fun i => RuntimeBitLength.Target.fullImage X L 0 F r i.val⟩ := by
      fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "Path.execute" => have ex := OLD path fit
      fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "outcome" => dsimp only [OLD] at ex
      have zero : bitLength 0=0 := rfl
      simpa only [initial,zero,if_pos (Nat.zero_le r)] using ex
    have first : ∀ u, u < b → ((Cursor.machine k).run u
        (⟨Cursor.q k 209,⟨L,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 329 := by
      apply control_before _ (Or.inr ⟨rfl,rfl⟩) (Or.inr (by change 201    ≤    209 ∧ 209    ≤    308 ∧ (209    ≤    250 ∨ 254    ≤    209) ∧ (209    ≤    304 ∨ 308    ≤    209); omega))
      intro u hu
      fromDonor "BitLengthDriver.Kernel" "BitLengthDriver" "Path.first" => have fs := OLD path fit u hu
      have fs' : ((Cursor.machine k).run u
          (⟨Cursor.q k 209,⟨L,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val  ≠  250 ∧
          ((Cursor.machine k).run u (⟨Cursor.q k 209,⟨L,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val  ≠  304 ∧
          ((Cursor.machine k).run u (⟨Cursor.q k 209,⟨L,by omega⟩,fun i => X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val  ≠  308 := by
        simpa only [initial] using fs
      exact ⟨fs'.2.2,fun _ => ⟨fs'.1,fs'.2.1⟩⟩
    have z : bitLength 0=0 := rfl
    have endFit : (if bitLength 0  ≤  r then L else F+r+0+3) < tapeLength N B := by
      rw [z,if_pos (Nat.zero_le r)]; omega
    refine ⟨a+b,endFit,?_,?_,?_⟩
    · have le : 1    ≤    (0+r+1)^2 := by nlinarith only [Nat.zero_le r,Nat.zero_le (r^2)]
      have mul := Nat.mul_le_mul_right (4096*(F+5*r+0+8)) le
      nlinarith only [ha,hb,mul,Nat.zero_le (F+5*r+0+8)]
    · intro u hu
      by_cases early : u < a
      · exact (prior u early).trans (by decide)
      · rw [show u=a+(u-a) by omega,UniformTM.run_add,enter]; exact first (u-a) (by omega)
    · have run : (Cursor.machine k).run (a+b) C=
          (⟨Cursor.q k 308,⟨L,by omega⟩,fun i => RuntimeBitLength.Target.fullImage X L 0 F r i.val⟩ : Config (Cursor.machine k).stateCount N B) := by
        rw [UniformTM.run_add,enter,finish]
      simpa only [z,if_pos (Nat.zero_le r)] using run
private structure Cells (V : Nat → Option Bool) (S z n A Q F : Nat) : Prop where
  arena : S+z+n+3+Q < F
  source : ∀ i, A     ≤     i → i < S → ∃ b, V i=some b
  eof : V S=none
  reg : ∀ i, S < i → i < S+z+2 → V i=some false
  sep : V (S+z+2)=none
  assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, V i=some b
  right : V (S+z+n+3)=none
  marks : ∀ i, S+z+n+3 < i → i     ≤     S+z+n+3+Q → V i=some true
  gap : ∀ i, S+z+n+3+Q < i → i < F → V i=none
  fence : V F=some false
/-- Ordinary application of B's exact immutable private theorem, with the full
expected cells proposition written here. No proof is supplied to the machine. -/
private theorem actual_cells {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n     ≤     FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let R := pairLength a m
    let B := FixedRawLengthFence.allocation R
    let S := a+m
    let F := FixedRawLengthFence.fencePos R
    let p := min (9+2*z+2^n) S
    let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
    let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    Cells V S z n (9+2*z) (2^n) F ∧ F+(S-p)+2 < tapeLength R B ∧
      (∀ i : Fin (tapeLength R B), F < i.val → V i.val=none) := by
  run_tac do
    let env ← getEnv
    let selected ← PartAPrivateRuntime.select `AllArityCounted.Runtime `AllArityCounted.actual_cells
    let names := [selected]
    logInfo m!"private-term|{names.head!}"
    let fields : List String := ["arena","source","eof","reg","sep","assn","right","marks","gap","fence"]
    let mut mapping := [("OLD",names.head!)]
    for field in fields do
      let user := Name.str `AllArityCounted.Cells field
      let selected ← PartAPrivateRuntime.select `AllArityCounted.Runtime user
      let found := [selected]
      logInfo m!"private-term|{found.head!}"
      mapping := mapping ++ [("OLD_"++field,found.head!)]
    let src := "(obtain ⟨fr,fit,fresh⟩ := OLD x w gamma cap rows; exact ⟨⟨OLD_arena fr,OLD_source fr,OLD_eof fr,OLD_reg fr,OLD_sep fr,OLD_assn fr,OLD_right fr,OLD_marks fr,OLD_gap fr,OLD_fence fr⟩,fit,fresh⟩)"
    let ast ← ofExcept (Parser.runParserCategory env `tactic src)
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1 == stx.getId.toString) with
        | some (_,name) => mkIdent name
        | none => stx
      else stx)
theorem accepted_seed (k : Nat) : Target.AcceptedSeed k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,z,t,hH,gamma,price,hp,pre,prefixBound,physicalStage,eofStage⟩ :=
    AllArityWorkspace.accepted_raw k x w accepted
  let R := pairLength a m; let B := FixedRawLengthFence.allocation R; let S := a+m
  let n := pr.2.n; let L := S+z+2; let F := FixedRawLengthFence.fencePos R
  let p := min (9+2*z+2^n) S; let r := S-p
  let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let C := SuffixCap.Target.image V F r
  let X := CappedWorkspace.Target.image C L n F r
  let Y := RuntimeBitLength.Target.fullImage X L n F r
  let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
  have pair : S    ≤    R := by dsimp only [S,R,pairLength]; omega
  have width : n    ≤    S := by
    have lt := Nat.lt_two_pow_self (n:=n)
    change 2^n    ≤    S at table
    omega
  have cap := AcceptedBody.strict_capacity x w gamma width
  have rows := Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨frame,shortFit,fresh⟩ := actual_cells x w gamma cap rows
  change Cells V S z n (9+2*z) (2^n) F at frame
  change F+r+2 < tapeLength R B at shortFit
  change ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none at fresh
  have Hval : L+n+1=S+z+n+3 := by dsimp only [L]; omega
  have geom : L+n+1+2^n < F := by have h := frame.arena; omega
  have geo : L+n+1 < F := lt_of_le_of_lt (Nat.le_add_right _ _) geom
  have oldC (i : Nat) (hi : i    ≤    F+1) : C i=V i := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_neg (by omega)]
  have cf : C F=some false := by rw [oldC _ (by omega)]; exact frame.fence
  have cd0 : C (F+1)=none := by
    rw [oldC _ (by omega)]
    exact fresh ⟨F+1,by clear * - shortFit; omega⟩ (Nat.lt_succ_self F)
  have cb0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : C i=some true := by
    dsimp only [C,SuffixCap.Target.image]; rw [if_pos (by omega)]
  refine ⟨pr,parsed,table,z,hH,gamma,?_,?_⟩
  · intro virtual
    obtain ⟨time,logical,implicitFalse,done,_safe⟩ := eofStage virtual
    exact ⟨_,clock R n r _ 0 0 (width.trans pair) ((Nat.sub_le S p).trans pair) time (by positivity) (by positivity),logical,implicitFalse,done⟩
  · intro physical
    change ∃ (t' : Nat)
      (h : (if bitLength n  ≤  r then F+2*r+n+4 else F+r+n+3) < tapeLength R B),
      t' ≤ 67108864*(R+1)^4 ∧ F+5*r+n+7 < tapeLength R B ∧
      (AllArityCursor.machine k).run t' c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
          ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,h⟩,
          fun i => (if bitLength n ≤ r then Target.seedImage Y F r n else Y) i.val⟩ ∧
      (∀ u, u < t' → ((AllArityCursor.machine k).run u c).state ≠
        SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 329)) ∧
      (r < bitLength n → S < Cursor.Target.M k n z)
    have phys : p < S := physical
    have rp : 0 < r := by dsimp only [r]; omega
    have pe : p=9+2*z+2^n := Nat.min_eq_left (by dsimp only [p] at phys; omega)
    obtain ⟨hS,counted,_firstCount,v,_hF,_bodyPrice,rawPrice,Pfit,workspace,firstWorkspace,_safe⟩ := physicalStage physical
    let d := 2+r*(2*(F-p)+6)
    change F+5*r+n+7 < tapeLength R B at Pfit
    change t+d+v    ≤    1048576*(R+1)^3 at rawPrice
    change (AllArityCursor.machine k).run (t+d) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.rReady k,⟨S,hS⟩,fun i => C i.val⟩ at counted
    change (AllArityCursor.machine k).run (t+d+v) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 201,⟨F+1,_hF⟩,fun i => X i.val⟩ at workspace
    change ∀ u, u < t+d+v → ((AllArityCursor.machine k).run u c).state   ≠
      SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 201) at firstWorkspace
    have blank (i : Nat) (lo : F+r+2    ≤    i) (hi : i    ≤    F+5*r+n+7) : C i=none := by
      dsimp only [C,SuffixCap.Target.image]; rw [if_neg (by omega)]
      exact fresh ⟨i,by clear * - hi Pfit; omega⟩ (by change F < i; omega)
    obtain ⟨xa,xf,xb0,xzero,xd,xold⟩ := AllArityWorkspace.six_bank_image C L n F r geo cf cd0 cb0 blank
    change ∀ i, i   ≤   L ∨ (L+n+1   ≤   i ∧ i   ≤   F+1) ∨ F+5*r+n+7   ≤   i → X i=C i at xold
    have xsep : X L=none := by
      rw [xold L (Or.inl le_rfl),oldC L (by omega)]
      exact frame.sep
    have xright : X (L+n+1)=none := by
      rw [xold (L+n+1) (Or.inr (Or.inl ⟨le_rfl,by omega⟩)),oldC (L+n+1) (by omega)]
      rw [Hval]; exact frame.right
    have xmarks (i : Nat) (lo : L+n+1 < i) (hi : i    ≤    L+n+1+2^n) : X i=some true := by
      rw [xold i (Or.inr (Or.inl ⟨Nat.le_of_lt lo,by omega⟩)),oldC i (by omega)]
      exact frame.marks i (by rw [← Hval]; exact lo) (by rw [← Hval]; exact hi)
    have xgap (i : Nat) (lo : L+n+1+2^n < i) (hi : i < F) : X i=none := by
      rw [xold i (Or.inr (Or.inl ⟨(Nat.le_add_right (L+n+1) (2^n)).trans (Nat.le_of_lt lo),by omega⟩)),oldC i (by omega)]
      exact frame.gap i (by rw [← Hval]; exact lo) hi
    have xbank1 (i : Nat) (lo : F+r+2 < i) (hi : i < F+r+n+3) : X i=some false := xzero i (Or.inl ⟨lo,hi⟩)
    have xbank2 (i : Nat) (lo : F+r+n+3 < i) (hi : i < F+2*r+n+4) : X i=some false := xzero i (Or.inr (Or.inl ⟨lo,hi⟩))
    obtain ⟨b,hb,bodyPrice,beforeBody,bodyRun⟩ := body k R B L n (2^n) F r X rp (by positivity) geom xsep xa xright xmarks xgap xf
      (xd _ (Or.inl rfl)) xb0 (xd _ (Or.inr (Or.inl rfl))) xbank1 (xd _ (Or.inr (Or.inr (Or.inl rfl)))) xbank2
      (xd _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) Pfit
    have pbase : 9+2*z  ≤  p := by rw [pe]; exact Nat.le_add_right _ _
    have countBound : ∀ u, u < d → ((Cursor.machine k).run u
        (⟨Cursor.q k 58,⟨p,hp⟩,fun i => V i.val⟩ : Config (Cursor.machine k).stateCount R B)).state.val < 98 := by
      fromDonor "AllArityWorkspace.Runtime" "AllArityWorkspace" "suffix_bound" =>
        exact OLD k R B p S z n (2^n) F V (by rw [pe]; positivity) phys (by positivity) frame.arena
          (by intro i lo hi; exact frame.source i (pbase.trans lo) hi)
          frame.eof frame.reg frame.sep frame.assn frame.right frame.marks frame.gap frame.fence
          (by intro i lo hi; exact fresh ⟨i,by clear * - hi shortFit; omega⟩ lo) shortFit
    have ep := pre
    change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ at ep
    rw [if_neg (Nat.ne_of_lt phys)] at ep
    have setupBefore : ∀ u, u < v → ((Cursor.machine k).run u
        (⟨Cursor.rReady k,⟨S,hS⟩,fun i => C i.val⟩ : Config (Cursor.machine k).stateCount R B)).state.val < 329 := by
      apply control_before _ (Or.inl ⟨rfl,rfl⟩) (Or.inr (by change 98    ≤    98 ∧ 98    ≤    201 ∧ (98    ≤    250 ∨ 254    ≤    98) ∧ (98    ≤    304 ∨ 308    ≤    98); omega))
      intro u hu
      refine ⟨?_,by intro bad; omega⟩
      intro bad
      apply firstWorkspace (t+d+u) (by omega)
      rw [show t+d+u=(t+d)+u by rfl,UniformTM.run_add,counted,right_run]
      apply Fin.ext
      change 288+_=288+_
      rw [bad]
      rfl
    have prior329 : ∀ u, u < t+d+v → ((AllArityCursor.machine k).run u c).state.val < 617 := by
      intro u hu
      by_cases early : u < t
      · exact (prefixBound u early).trans (by decide)
      · by_cases counting : u < t+d
        · have bd := countBound (u-t) (by omega)
          rw [show u=t+(u-t) by omega,UniformTM.run_add,ep,right_run]
          change 288+_ < 617
          exact (Nat.add_lt_add_left bd 288).trans (by decide : 386 < 617)
        · have bd := setupBefore (u-(t+d)) (by omega)
          rw [show u=(t+d)+(u-(t+d)) by omega,UniformTM.run_add,counted,right_run]
          change 288+_ < 617
          exact Nat.add_lt_add_left bd 288
    have doneBody : (AllArityCursor.machine k).run (t+d+v+b) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k (if bitLength n    ≤    r then 308 else if (r+1)%2=1 then 250 else 304),
          ⟨if bitLength n    ≤    r then L else F+r+n+3,hb⟩,fun i => Y i.val⟩ := by
      rw [UniformTM.run_add,workspace,right_run,bodyRun]
    have firstBody : ∀ u, u < t+d+v+b → ((AllArityCursor.machine k).run u c).state.val < 617 := by
      intro u hu
      by_cases early : u < t+d+v
      · exact prior329 u early
      · have bd := beforeBody (u-(t+d+v)) (by omega)
        rw [show u=(t+d+v)+(u-(t+d+v)) by omega,UniformTM.run_add,workspace,right_run]
        change 288+_ < 617
        exact Nat.add_lt_add_left bd 288
    have overflow : r < bitLength n → S < Cursor.Target.M k n z := by
      intro over
      have np : 0 < n := by
        by_contra bad
        have eq : n=0 := by omega
        have zero : bitLength n=0 := by rw [eq]; rfl
        omega
      exact overflow_address k n z S r np phys rfl over
    have outFit : (if bitLength n  ≤  r then F+2*r+n+4 else F+r+n+3) < tapeLength R B := by
      clear * - Pfit
      split <;> omega
    have headL : L < tapeLength R B := by clear * - geo Pfit; omega
    have headD3 : F+2*r+n+4 < tapeLength R B := by clear * - Pfit; omega
    by_cases fits : bitLength n    ≤    r
    · have reached : (AllArityCursor.machine k).run (t+d+v+b) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 308,⟨L,headL⟩,fun i => Y i.val⟩ := by
        simpa only [if_pos fits] using doneBody
      have oldY (i : Nat) (ha : i    ≤    L ∨ L+n+1    ≤    i) (h1 : i    ≤    F+r+2 ∨ F+r+n+3    ≤    i)
          (h2 : i    ≤    F+r+n+3 ∨ F+2*r+n+4    ≤    i) : Y i=X i := by
        dsimp only [Y,RuntimeBitLength.Target.fullImage]
        rw [if_neg (by omega),if_neg (by omega),if_neg (by have h := Nat.min_le_right (bitLength n) r; omega)]
      have yA (i : Nat) (lo : L < i) (hi : i < L+n+1) : ∃ b, Y i=some b := by
        dsimp only [Y,RuntimeBitLength.Target.fullImage]; rw [if_pos ⟨lo,hi⟩]; exact ⟨_,rfl⟩
      have yB (i : Nat) (lo : F+r+2 < i) (hi : i < F+r+n+3) : ∃ b, Y i=some b := by
        dsimp only [Y,RuntimeBitLength.Target.fullImage]; rw [if_neg (by omega),if_pos ⟨lo,hi⟩]; exact ⟨_,rfl⟩
      have yC (i : Nat) (lo : F+r+n+3 < i) (hi : i < F+2*r+n+4) : ∃ b, Y i=some b := by
        dsimp only [Y,RuntimeBitLength.Target.fullImage]; rw [if_neg (by omega),if_neg (by omega)]
        by_cases mark : i    ≤    F+r+n+3+min (bitLength n) r
        · rw [if_pos ⟨lo,mark⟩]; exact ⟨true,rfl⟩
        · rw [if_neg (by omega),xbank2 i lo hi]; exact ⟨false,rfl⟩
      have yd (i : Nat) (di : i=F+1 ∨ i=F+r+2 ∨ i=F+r+n+3 ∨ i=F+2*r+n+4) : Y i=none := by
        rw [oldY i (by omega) (by omega) (by omega)]; apply xd i; omega
      obtain ⟨s,seedPrice,seedRun,seedFirst⟩ := seed k R B L n (2^n) F r Y rp geom
        (by rw [oldY L (by omega) (by omega) (by omega)]; exact xsep) yA
        (by rw [oldY (L+n+1) (by omega) (by omega) (by omega)]; exact xright)
        (by intro i lo hi; rw [oldY i (by omega) (by omega) (by omega)]; by_cases marks : i    ≤    L+n+1+2^n; exact Or.inr (xmarks i lo marks); exact Or.inl (xgap i (by omega) hi))
        (by rw [oldY F (by omega) (by omega) (by omega)]; exact xf)
        (yd _ (Or.inl rfl)) (by intro i lo hi; rw [oldY i (by omega) (by omega) (by omega)]; exact ⟨true,xb0 i lo hi⟩)
        (yd _ (Or.inr (Or.inl rfl))) yB (yd _ (Or.inr (Or.inr (Or.inl rfl)))) yC
        (yd _ (Or.inr (Or.inr (Or.inr rfl))))
        (by rw [oldY _ (by omega) (by omega) (by omega)]; exact xzero _ (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩)))) Pfit
      refine ⟨t+d+v+b+s,outFit,clock R n r _ b s (width.trans pair) ((Nat.sub_le S p).trans pair) rawPrice bodyPrice seedPrice,Pfit,?_,?_,overflow⟩
      · have run : (AllArityCursor.machine k).run (t+d+v+b+s) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k 329,⟨F+2*r+n+4,headD3⟩,fun i => Target.seedImage Y F r n i.val⟩ := by
          rw [UniformTM.run_add,reached,right_run,seedRun]
        simpa only [if_pos fits] using run
      · intro u hu eq
        have ev := congrArg Fin.val eq
        have sv : (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 329)).val=617 := by change 288+329%Cursor.stateCount k=617; rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
        rw [sv] at ev
        by_cases early : u < t+d+v+b
        · exact (Nat.ne_of_lt (firstBody u early)) ev
        · have bd := seedFirst (u-(t+d+v+b)) (by omega)
          rw [show u=(t+d+v+b)+(u-(t+d+v+b)) by omega,UniformTM.run_add,reached,right_run] at ev
          change 288+_=288+329 at ev
          exact (Nat.ne_of_lt bd) (Nat.add_left_cancel ev)
    · refine ⟨t+d+v+b,outFit,clock R n r _ b 0 (width.trans pair) ((Nat.sub_le S p).trans pair) rawPrice bodyPrice (by positivity),Pfit,?_,?_,overflow⟩
      · simpa only [if_neg fits] using doneBody
      · intro u hu eq
        have bd := firstBody u hu
        have ev := congrArg Fin.val eq
        change _=288+329%Cursor.stateCount k at ev
        rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)] at ev
        exact (Nat.ne_of_lt bd) ev
end AllArityBitLength
