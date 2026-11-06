import Complexity.PrivateInterfaceLookupResolvedRuntime
import AllArityCounted.Target
namespace AllArityCounted
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open Lean Elab Tactic
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private theorem clocks (R S z n p t : Nat) (hS : S ≤ R) (hz : z ≤ R) (hn : n ≤ R)
    (price : t ≤ 4096*(R+1)^2) :
    t+(2+(S-p)*(2*((3*R+2)-p)+6)) ≤ 65536*(R+1)^2 ∧
    t+(z+n+5) ≤ 65536*(R+1)^2 := by
  have rem : S-p ≤ R := (Nat.sub_le _ _).trans hS
  have body : 2+(S-p)*(2*((3*R+2)-p)+6) ≤ 16*(R+1)^2 := by
    calc
      _ ≤ 2+R*(2*(3*R+2)+6) := Nat.add_le_add_left
        (Nat.mul_le_mul rem (Nat.add_le_add_right
          (Nat.mul_le_mul_left 2 (Nat.sub_le (3*R+2) p)) 6)) 2
      _ ≤ 16*(R+1)^2 := by nlinarith
  constructor <;> nlinarith only [price,body,hz,hn,Nat.zero_le (R*R)]
/-- Exact existing EOF body, including empty assignment banks. This is an
endpoint theorem; no first-MReady claim is made. -/
theorem eof_body (k : Nat) {N B : Nat} (V : Nat → Option Bool) (S z n : Nat)
    (fit : S+z+n+3 < tapeLength N B) (eof : V S=none)
    (reg : ∀ i, S < i → i < S+z+2 → V i=some false) (sep : V (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, V i=some b)
    (right : V (S+z+n+3)=none) :
    (Cursor.machine k).run (z+n+5)
      (⟨Cursor.q k 57,⟨S,by omega⟩,fun i => V i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,fit⟩,fun i => V i.val⟩ := by
  run_tac do
    let name ← PartAPrivateRuntime.select `Cursor.Proof `Cursor.eof_kernel
    let id := mkIdent name
    let kv := mkIdent `k; let vv := mkIdent `V; let sv := mkIdent `S
    let zv := mkIdent `z; let nv := mkIdent `n; let fv := mkIdent `fit
    let ev := mkIdent `eof; let rv := mkIdent `reg; let sepv := mkIdent `sep
    let av := mkIdent `assn; let rightv := mkIdent `right
    evalTactic (← `(tactic| exact $id:ident $kv:ident $vv:ident $sv:ident $zv:ident $nv:ident
      $fv:ident $ev:ident $rv:ident $sepv:ident $av:ident $rightv:ident))
private structure Cells (V : Nat → Option Bool) (S z n A Q F : Nat) : Prop where
  arena : S+z+n+3+Q < F
  source : ∀ i, A ≤ i → i < S → ∃ b, V i=some b
  eof : V S=none
  reg : ∀ i, S < i → i < S+z+2 → V i=some false
  sep : V (S+z+2)=none
  assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, V i=some b
  right : V (S+z+n+3)=none
  marks : ∀ i, S+z+n+3 < i → i ≤ S+z+n+3+Q → V i=some true
  gap : ∀ i, S+z+n+3+Q < i → i < F → V i=none
  fence : V F=some false
/-- The genuine n0 hole is retained: equality is only above cell7. -/
private theorem installed_high {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (z n i : Nat) (above : 7 < i) :
    Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (a+m+z+2) n) i=
      Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 n) (a+m+z+2) n) i := by
  dsimp only [Body.extend]
  split_ifs
  · dsimp only [Body.installedTape]
    split_ifs
    · rfl
    · dsimp only [SmallIngress.prepared]
      rw [if_neg (by omega)]
  · rfl
private theorem image_high {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m)
    (z n i : Nat) (above : 7 < i) :
    Stream.Target.image
      (Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (a+m+z+2) n))
      (a+m) z n (9+2*z) (2^n) (2^n) false i=
    Stream.Target.image
      (Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 n) (a+m+z+2) n))
      (a+m) z n (9+2*z) (2^n) (2^n) false i := by
  dsimp only [Stream.Target.image]
  split_ifs <;> first | rfl | exact installed_high B x w z n i above
private theorem shrink_tail (F r n L : Nat) (h : F+5*r+n+7 < L) : F+r+2 < L := by omega
private theorem actual_cells {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let R := pairLength a m
    let B := FixedRawLengthFence.allocation R
    let S := a+m
    let F := FixedRawLengthFence.fencePos R
    let p := min (9+2*z+2^n) S
    let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
    let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    Cells V S z n (9+2*z) (2^n) F ∧ F+(S-p)+2 < tapeLength R B ∧
      (∀ i : Fin (tapeLength R B), F < i.val → V i.val=none) := by
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let F := FixedRawLengthFence.fencePos R
  let p := min (9+2*z+2^n) S
  let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  have gammaSupport := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  obtain ⟨geom,scratch,hF,fence⟩ := Stream.raw_budget_cells x w gamma cap
  have geo : S+z+n+3 < F := geom
  have fitF : F < tapeLength R B := hF
  have hH : S+z+n+3 < tapeLength R B := geo.trans fitF
  have arena : S+z+n+3+2^n < F := by change 2^n ≤ F-(S+z+n+3)-1 at rows; omega
  have low (i : Nat) (hi : i ≤ S+z+2) : V i=U i := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    rfl
  have oldU (i : Nat) (hi : i < tapeLength R B) (above : 7 < i) :
      U i=Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 n) (S+z+2) n ⟨i,hi⟩ := by
    change Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (a+m+z+2) n) i=_
    rw [installed_high B x w z n i above]
    exact Body.extend_read _ ⟨i,hi⟩
  have oldLow (i : Nat) (hi : i ≤ S+z+2) (above : 7 < i) :
      V i=FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,by change i < tapeLength R B; omega⟩ := by
    rw [low i hi,oldU i (by omega) above]
    dsimp only [Body.installedTape]
    rw [if_neg (by omega)]
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma
    (FixedRawLengthFence.resource_bounds R).1 (Nat.le_of_lt cap)
  have source (i : Nat) (lo : 9+2*z ≤ i) (hi : i < S) : ∃ b, V i=some b := by
    rw [oldLow i (by omega) (by omega)]
    exact ⟨_,Body.raw_source_after_header x w gamma (FixedRawLengthFence.resource_bounds R).1
      (Nat.le_of_lt cap) ⟨i,by change i < tapeLength R B; omega⟩ (by change 8+2*z+1 ≤ i; omega) hi⟩
  have eof : V S=none := by
    rw [oldLow S (by omega) (by dsimp only [S]; omega)]
    unfold FixedRawLengthFence.countdownTape
    rw [if_neg (by change S≠F; omega)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
  have reg (i : Nat) (lo : S < i) (hi : i < S+z+2) : V i=some false := by
    rw [oldLow i (by omega) (by dsimp only [S] at lo; omega)]
    exact cells.2.1 (i-S-1) (by omega) _ (by change i=a+m+1+(i-S-1); dsimp only [S] at lo; omega)
  have sep : V (S+z+2)=none := by
    rw [oldLow _ le_rfl (by dsimp only [S]; omega)]
    exact cells.2.2.1 _ (by dsimp only [S]; omega)
  have assn (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : ∃ b, V i=some b := by
    dsimp only [V,Stream.Target.image]
    rw [if_pos (by omega)]
    exact ⟨_,rfl⟩
  have right : V (S+z+n+3)=none := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    change U (S+z+n+3)=none
    rw [oldU _ hH (by dsimp only [S]; omega)]
    exact scratch _ (by change S+z+n+3 ≤ S+z+n+3; rfl) geo
  have marks (i : Nat) (lo : S+z+n+3 < i) (hi : i ≤ S+z+n+3+2^n) : V i=some true := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_pos (by constructor <;> omega)]
  have gap (i : Nat) (lo : S+z+n+3+2^n < i) (hi : i < F) : V i=none := by
    have afterH : S+z+n+3 < i := lt_of_le_of_lt (Nat.le_add_right _ _) lo
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by clear * - afterH; omega),if_neg (by clear * - lo; omega)]
    change U i=none
    rw [oldU _ (hi.trans fitF) (by clear * - afterH gammaSupport; dsimp only [S] at *; omega)]
    exact scratch _ (Nat.le_of_lt afterH) hi
  have vf : V F=some false := by
    dsimp only [V,Stream.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    change U F=some false
    rw [oldU _ fitF (by dsimp only [S] at geo; omega)]
    exact fence
  obtain ⟨legacyFresh,tailfit⟩ := Cursor.raw_tail_blank x w gamma cap rows
  change F+5*(S-p)+n+7 < tapeLength R B at tailfit
  have fresh (i : Fin (tapeLength R B)) (hi : F < i.val) : V i.val=none := by
    change Stream.Target.image
      (Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (a+m+z+2) n))
      (a+m) z n (9+2*z) (2^n) (2^n) false i.val=none
    rw [image_high B x w z n i.val (by clear * - geo hi gammaSupport; dsimp only [S] at *; omega)]
    exact legacyFresh i hi
  exact ⟨⟨arena,source,eof,reg,sep,assn,right,marks,gap,vf⟩,shrink_tail F (S-p) n _ tailfit,fresh⟩

private theorem cursor_left (A Q S : Nat) (h : min (A+Q) S < S) : min (A+Q) S=A+Q :=
  Nat.min_eq_left (by omega)
private theorem raw_values (k : Nat) :
    (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k)).val=386 ∧
    328 < (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)).val := by
  constructor
  · change 288+98 % Cursor.stateCount k=386
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
  · change 328 < 288+((64+265+82*k+1+11*k)+604+2) % Cursor.stateCount k
    rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
    omega
private theorem no_prior (A : UniformTM) {N B : Nat} (c : Config A.stateCount N B)
    (t : Nat) (outside : (A.run t c).state≠A.accept ∧ (A.run t c).state≠A.reject) :
    ∀ u, u ≤ t → (A.run u c).state≠A.accept ∧ (A.run u c).state≠A.reject := by
  intro u hu
  constructor
  · intro h
    have later : A.run t c=A.run u c := by
      rw [show t=u+(t-u) by omega,A.run_add]
      exact A.run_accept _ h _
    exact outside.1 (by rw [later]; exact h)
  · intro h
    have later : A.run t c=A.run u c := by
      rw [show t=u+(t-u) by omega,A.run_add]
      exact A.run_reject _ h _
    exact outside.2 (by rw [later]; exact h)
private theorem no_verdict (k : Nat) {N B : Nat} (c : Config (AllArityCursor.machine k).stateCount N B)
    (t : Nat) (outside : ((AllArityCursor.machine k).run t c).state.val≠327 ∧
      ((AllArityCursor.machine k).run t c).state.val≠328) :
    ∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
      ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject := by
  apply no_prior
  constructor
  · intro h
    have e := congrArg Fin.val h
    rw [(AllArityCursor.control_values k).2.2.1] at e
    exact outside.1 e
  · intro h
    have e := congrArg Fin.val h
    rw [(AllArityCursor.control_values k).2.2.2] at e
    exact outside.2 e
/-- ALL-ARITY actual raw composition: strict FIRST COUNTED on physical source,
and the exact virtual EOF MReady endpoint, on the unchanged producer288 family. -/
theorem accepted_raw (k : Nat) : Target.AcceptedRaw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,z,T,t,hH,gamma,oldPrice,ht,_twoPrice,hp,_hp1,_old,_oldFirst,path,_absent,_paid,pre,_eof,_physical⟩ :=
    AllArityCursor.accepted_raw k x w accepted
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let n := pr.2.n
  let F := FixedRawLengthFence.fencePos R
  let p := min (9+2*z+2^n) S
  let r := S-p
  let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (S+z+2) n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
  have price : t ≤ 4096*(R+1)^2 := ht.trans oldPrice
  have pair : S ≤ R := by dsimp only [S,R,pairLength]; omega
  have gammaSupport := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  have zz : z ≤ R := by change 8+z < S at gammaSupport; omega
  have width : n ≤ S := by
    have lt := Nat.lt_two_pow_self (n := n)
    change 2^n ≤ S at table
    omega
  have cap := AcceptedBody.strict_capacity x w gamma width
  have rows := Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨frame,tailfit,fresh⟩ := actual_cells x w gamma cap rows
  have bounds := clocks R S z n p t pair zz (width.trans pair) price
  have headFit : S < tapeLength R B := by
    have hh : S+z+n+3 < tapeLength R B := hH
    clear * - hh
    omega
  have prefixBound (u : Nat) (hu : u < t) : ((AllArityCursor.machine k).run u c).state.val < 352 := by
    rw [path u (by omega)]
    change (SmallIngress.machine.run u (initialConfig SmallIngress.machine B (encodePair x w))).state.val < 352
    exact (SmallIngress.machine.run u (initialConfig SmallIngress.machine B (encodePair x w))).state.isLt
  refine ⟨pr,parsed,table,z,t,hH,gamma,price,hp,pre,prefixBound,?_,?_⟩
  · intro physical
    have physical' : p < S := physical
    have pe : p=9+2*z+2^n := cursor_left (9+2*z) (2^n) S physical'
    have pos : 0 < p := by rw [pe]; positivity
    have above : 9+2*z ≤ p := by rw [pe]; exact Nat.le_add_right _ _
    have source (i : Nat) (lo : p ≤ i) (hi : i < S) : ∃ b, V i=some b :=
      frame.source i (above.trans lo) hi
    have fitTail : F+r+2 < tapeLength R B := tailfit
    have blankHigh (i : Nat) (lo : F < i) (hi : i ≤ F+r+2) : V i=none :=
      fresh ⟨i,lt_of_le_of_lt hi fitTail⟩ lo
    have kernel := SuffixCap.counted k R B p S z n (2^n) F V pos physical'
      (by positivity) frame.arena source frame.eof frame.reg frame.sep frame.assn
      frame.right frame.marks frame.gap frame.fence blankHigh tailfit
    have ep := pre
    change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ at ep
    rw [if_neg (Nat.ne_of_lt physical')] at ep
    let cost := 2+r*(2*(F-p)+6)
    have done : (AllArityCursor.machine k).run (t+cost) c=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.rReady k,⟨S,headFit⟩,
            fun i => SuffixCap.Target.image V F r i.val⟩ := by
      rw [UniformTM.run_add,ep]
      change (SmallIngress.producer.seq (Cursor.machine k)).run cost _=_
      rw [UniformTM.seq_run_right,kernel.1]
    have first (u : Nat) (hu : u < t+cost) : ((AllArityCursor.machine k).run u c).state≠
        SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k) := by
      intro eq
      by_cases before : u < t
      · have lim := prefixBound u before
        rw [eq,(raw_values k).1] at lim
        omega
      · have avoid := kernel.2 (u-t) (by dsimp only [cost,r] at hu; omega)
        apply avoid
        have ev := congrArg Fin.val eq
        rw [show u=t+(u-t) by omega,UniformTM.run_add,ep] at ev
        change ((SmallIngress.producer.seq (Cursor.machine k)).run (u-t)
          (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k 58,⟨p,hp⟩,fun i => V i.val⟩)).state.val=_ at ev
        rw [UniformTM.seq_run_right] at ev
        apply Fin.ext
        change 288+_=288+_ at ev
        exact Nat.add_left_cancel ev
    have safe := no_verdict k c (t+cost) (by
      rw [done]
      change (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k)).val≠327 ∧
        (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.rReady k)).val≠328
      rw [(raw_values k).1]
      constructor <;> decide)
    refine ⟨_,tailfit,?_,first,done,safe⟩
    exact bounds.1
  · intro virtual
    have pc : p=S := virtual
    have ep := pre
    change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ at ep
    simp only [pc,↓reduceIte] at ep
    have kernel := eof_body k V S z n hH frame.eof frame.reg frame.sep frame.assn frame.right
    have done : (AllArityCursor.machine k).run (t+(z+n+5)) c=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩ := by
      rw [UniformTM.run_add,ep]
      change (SmallIngress.producer.seq (Cursor.machine k)).run (z+n+5) _=_
      rw [UniformTM.seq_run_right,kernel]
    have safe := no_verdict k c (t+(z+n+5)) (by
      rw [done]
      have hi := (raw_values k).2
      change (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)).val≠327 ∧
        (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)).val≠328
      omega)
    have logical : S ≤ Cursor.Target.M k n z := by
      have endBound : S ≤ 9+2*z+2^n := by clear * - pc; dsimp only [p] at pc; omega
      unfold Cursor.Target.M
      omega
    have implicitFalse : padRead (Fin.append x w) (Cursor.Target.M k n z)=false := by
      unfold padRead
      rw [dif_neg (by change ¬Cursor.Target.M k n z < S; omega)]
    exact ⟨bounds.2,logical,implicitFalse,done,safe⟩
end AllArityCounted
