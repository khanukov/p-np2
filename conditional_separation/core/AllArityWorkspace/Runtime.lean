import Complexity.PrivateInterfaceLookupResolvedRuntime
import AllArityWorkspace.Target
namespace AllArityWorkspace
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Tactic
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private theorem clocks (R n r ct v : Nat) (hn : n ≤ R) (hr : r ≤ R)
    (hc : ct ≤ 65536*(R+1)^2) (hv : v ≤ 128*(n+r+1)*(3*R+2+5*r+n+9)) :
    ct+v ≤ 1048576*(R+1)^3 := by
  have c1 : n+r+1 ≤ 8*(R+1) := by omega
  have c2 : 3*R+2+5*r+n+9 ≤ 18*(R+1) := by omega
  have body : v ≤ 32768*(R+1)^2 := by
    calc
      v ≤ 128*(n+r+1)*(3*R+2+5*r+n+9) := hv
      _ ≤ 128*(8*(R+1))*(18*(R+1)) := Nat.mul_le_mul (Nat.mul_le_mul_left 128 c1) c2
      _ ≤ 32768*(R+1)^2 := by nlinarith only [Nat.zero_le ((R+1)^2)]
  nlinarith only [hc,body,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
private theorem eof_clock (R u : Nat) (h : u ≤ 65536*(R+1)^2) :
    u ≤ 1048576*(R+1)^3 := by
  nlinarith only [h,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
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
/-- Ordinary application of B's exact immutable private theorem, with the full
expected cells proposition written here. No proof is supplied to the machine. -/
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
  run_tac do
    let env ← getEnv
    let selected ← PartAPrivateRuntime.select `AllArityCounted.Runtime `AllArityCounted.actual_cells
    let names := [selected]
    let fields : List String := ["arena","source","eof","reg","sep","assn","right","marks","gap","fence"]
    let mut mapping := [("OLD",names.head!)]
    for field in fields do
      let user := Name.str `AllArityCounted.Cells field
      let selected ← PartAPrivateRuntime.select `AllArityCounted.Runtime user
      let found := [selected]
      mapping := mapping ++ [("OLD_"++field,found.head!)]
    let src := "(obtain ⟨fr,fit,fresh⟩ := OLD x w gamma cap rows; exact ⟨⟨OLD_arena fr,OLD_source fr,OLD_eof fr,OLD_reg fr,OLD_sep fr,OLD_assn fr,OLD_right fr,OLD_marks fr,OLD_gap fr,OLD_fence fr⟩,fit,fresh⟩)"
    let ast ← ofExcept (Parser.runParserCategory env `tactic src)
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent then
        match mapping.find? (fun p => p.1 == stx.getId.toString) with
        | some (_,name) => mkIdent name
        | none => stx
      else stx)
/-- Generic counted-path control bound from A, independent of its old raw wrapper. -/
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
    let selected ← PartAPrivateRuntime.select `CappedWorkspace.Raw `CappedWorkspace.suffix_bound
    let names := [selected]
    let src := "(exact OLD k N B p S z n Q F T pos physical paid room source eof reg sep assn right marks gap fence fresh fit)"
    let ast ← ofExcept (Parser.runParserCategory env `tactic src)
    evalTactic (ast.rewriteBottomUp fun stx =>
      if stx.isIdent && stx.getId.toString == "OLD" then mkIdent names.head! else stx)
private theorem raw_value (k : Nat) :
    (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 201)).val=489 := by
  change 288+201 % Cursor.stateCount k=489
  rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]
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
/-- ALL-ARITY raw origin, exact tape, first physical six-bank boundary, or executed
virtual EOF mode2. The concrete table and allocation are unchanged. -/
theorem accepted_raw (k : Nat) : Target.AcceptedRaw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,z,t,hH,gamma,price,hp,pre,prefixBound,physicalStage,eofStage⟩ :=
    AllArityCounted.accepted_raw k x w accepted
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let n := pr.2.n
  let L := S+z+2
  let F := FixedRawLengthFence.fencePos R
  let p := min (9+2*z+2^n) S
  let r := S-p
  let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let C := SuffixCap.Target.image V F r
  let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
  have pair : S ≤ R := by dsimp only [S,R,pairLength]; omega
  have width : n ≤ S := by
    have lt := Nat.lt_two_pow_self (n := n)
    change 2^n ≤ S at table
    omega
  have cap := AcceptedBody.strict_capacity x w gamma width
  have rows := Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨frame,_smallFit,fresh⟩ := actual_cells x w gamma cap rows
  obtain ⟨_legacyFresh,fullFit⟩ := Cursor.raw_tail_blank x w gamma cap rows
  have Pfit : F+5*r+n+7 < tapeLength R B := fullFit
  refine ⟨pr,parsed,table,z,t,hH,gamma,price,hp,pre,prefixBound,?_,?_⟩
  · intro physical
    have phys : p < S := physical
    obtain ⟨hS,shortFit,countPrice,firstCount,counted,_countSafe⟩ := physicalStage physical
    let d := 2+r*(2*(F-p)+6)
    have geom : S+z+n+3+2^n < F := frame.arena
    have geo : S+z+n+3 < F := lt_of_le_of_lt (Nat.le_add_right _ _) geom
    have oldC (i : Nat) (hi : i ≤ F+1) : C i=V i := by
      dsimp only [C,SuffixCap.Target.image]
      rw [if_neg (by omega)]
    have cEof : C S=none := by rw [oldC _ (by clear * - geo; omega)]; exact frame.eof
    have cReg (i : Nat) (lo : S < i) (hi : i < S+z+2) : C i=some false := by
      rw [oldC _ (by clear * - geo hi; omega)]; exact frame.reg i lo hi
    have cSep : C (S+z+2)=none := by rw [oldC _ (by clear * - geo; omega)]; exact frame.sep
    have cAssn (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : C i=some false := by
      rw [oldC _ (by clear * - geo hi; omega)]
      dsimp only [V,Stream.Target.image]
      rw [if_pos (by constructor <;> omega),CappedWorkspace.overflow_bits]
      simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
      split_ifs <;> rfl
    have cRight : C (S+z+n+3)=none := by rw [oldC _ (by clear * - geo; omega)]; exact frame.right
    have cMarks (i : Nat) (lo : S+z+n+3 < i) (hi : i ≤ S+z+n+3+2^n) : C i=some true := by
      rw [oldC _ (by omega)]; exact frame.marks i lo hi
    have cGap (i : Nat) (lo : S+z+n+3+2^n < i) (hi : i < F) : C i=none := by
      rw [oldC _ (by omega)]; exact frame.gap i lo hi
    have cFence : C F=some false := by rw [oldC _ (by omega)]; exact frame.fence
    have cD0 : C (F+1)=none := by
      rw [oldC _ (by omega)]
      exact fresh ⟨F+1,by change F+1 < tapeLength R B; omega⟩ (Nat.lt_succ_self F)
    have cBank0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : C i=some true := by
      dsimp only [C,SuffixCap.Target.image]; rw [if_pos (by omega)]
    have cFresh (i : Nat) (lo : F+r+2 ≤ i) (hi : i ≤ F+5*r+n+7) : C i=none := by
      dsimp only [C,SuffixCap.Target.image]
      rw [if_neg (by omega)]
      exact fresh ⟨i,by change i < tapeLength R B; clear * - hi Pfit; omega⟩ (by change F < i; clear * - lo; omega)
    obtain ⟨v,hv,runSetup,beforeSetup⟩ := CappedWorkspace.workspace k R B S L n (2^n) F r C
      (by dsimp only [L]; omega) (by positivity) (by dsimp only [L]; omega) cEof cReg cSep
      (by intro i lo hi; exact cAssn i lo (by dsimp only [L] at hi; omega))
      (by rw [show L+n+1=S+z+n+3 by dsimp only [L]; omega]; exact cRight)
      (by intro i lo hi; exact cMarks i (by dsimp only [L] at lo; omega) (by dsimp only [L] at hi; omega))
      (by intro i lo hi; exact cGap i (by dsimp only [L] at lo; omega) hi) cFence cD0 cBank0 cFresh Pfit
    have pe : p=9+2*z+2^n := Nat.min_eq_left (by dsimp only [p] at phys; omega)
    have pos : 0 < p := by rw [pe]; positivity
    have above : 9+2*z ≤ p := by rw [pe]; exact Nat.le_add_right _ _
    have source (i : Nat) (lo : p ≤ i) (hi : i < S) : ∃ b, V i=some b :=
      frame.source i (above.trans lo) hi
    have blankHigh (i : Nat) (lo : F < i) (hi : i ≤ F+r+2) : V i=none :=
      fresh ⟨i,lt_of_le_of_lt hi shortFit⟩ lo
    have countBound := suffix_bound k R B p S z n (2^n) F V pos phys
      (by positivity) frame.arena source frame.eof frame.reg frame.sep frame.assn
      frame.right frame.marks frame.gap frame.fence blankHigh shortFit
    have ep := pre
    change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ at ep
    rw [if_neg (Nat.ne_of_lt phys)] at ep
    have beforeCount : ∀ u, u < t+d → ((AllArityCursor.machine k).run u c).state.val < 386 := by
      intro u hu
      by_cases early : u < t
      · exact (prefixBound u early).trans_le (by decide)
      · have lim := countBound (u-t) (by dsimp only [d,r] at hu; omega)
        rw [show u=t+(u-t) by omega,UniformTM.run_add,ep]
        change ((SmallIngress.producer.seq (Cursor.machine k)).run (u-t) _).state.val < 386
        rw [UniformTM.seq_run_right]
        exact Nat.add_lt_add_left lim 288
    have done : (AllArityCursor.machine k).run (t+d+v) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.q k 201,⟨F+1,by change F+1 < tapeLength R B; clear * - Pfit; omega⟩,fun i => CappedWorkspace.Target.image C L n F r i.val⟩ := by
      rw [UniformTM.run_add,counted]
      change (SmallIngress.producer.seq (Cursor.machine k)).run v _=_
      rw [UniformTM.seq_run_right,runSetup]
    have first (u : Nat) (hu : u < t+d+v) : ((AllArityCursor.machine k).run u c).state≠
        SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 201) := by
      intro eq
      have ev := congrArg Fin.val eq
      rw [raw_value] at ev
      by_cases early : u < t+d
      · exact (Nat.ne_of_lt ((beforeCount u early).trans (by decide : 386 < 489))) ev
      · have lim := beforeSetup (u-(t+d)) (by omega)
        rw [show u=(t+d)+(u-(t+d)) by omega,UniformTM.run_add,counted] at ev
        change ((SmallIngress.producer.seq (Cursor.machine k)).run (u-(t+d)) _).state.val=489 at ev
        rw [UniformTM.seq_run_right] at ev
        have bad : ((Cursor.machine k).run (u-(t+d))
            (⟨Cursor.rReady k,⟨S,hS⟩,fun i => C i.val⟩ : Config (Cursor.machine k).stateCount R B)).state.val=201 :=
          Nat.add_left_cancel ev
        exact (Nat.ne_of_lt lim) bad
    have safe := no_prior (AllArityCursor.machine k) c (t+d+v) (by
      rw [done]
      constructor
      · intro h
        have e := congrArg Fin.val h
        change (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 201)).val=_ at e
        rw [raw_value,(AllArityCursor.control_values k).2.2.1] at e
        omega
      · intro h
        have e := congrArg Fin.val h
        change (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 201)).val=_ at e
        rw [raw_value,(AllArityCursor.control_values k).2.2.2] at e
        omega)
    refine ⟨hS,counted,firstCount,v,_,hv,?_,Pfit,done,first,safe⟩
    exact clocks R n r (t+d) v (width.trans pair) ((Nat.sub_le S p).trans pair) countPrice hv
  · intro virtual
    obtain ⟨priceEOF,logical,implicitFalse,done,safe⟩ := eofStage virtual
    exact ⟨eof_clock R _ priceEOF,logical,implicitFalse,done,safe⟩
end AllArityWorkspace
