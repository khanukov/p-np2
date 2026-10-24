import VirtualFinalClosure.GuardAdvance
import VirtualFinalClosure.GuardArithmeticRound
namespace VirtualFinalClosure.GuardDriver
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("PostWeight.Kernel","PostWeight","Banks.room","room",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.SL","sourceLow",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","digit","digit",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole","hole",0),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_banks","holeBanks",1),
      ("VirtualFinalClosure.GuardAdvance","VirtualFinalClosure.GuardAdvance","prepared","advance",1),
      ("VirtualFinalClosure.GuardArithmeticRound","VirtualFinalClosure.GuardArithmeticRound","prepared","arithmetic",1),
      ("VirtualFinalClosure.GuardUnary","VirtualFinalClosure.GuardUnary","ellDec","ellDec",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
/-- Proof-side value of the exact BIG-endian prefix. Runtime operands remain
only the actually traversed cells and finite carried mode. -/
private def value (bits : Nat → Bool) (S : Nat) : Nat → Nat → Nat → Nat
  | _,0,i=>i
  | h,ell+1,i=>value bits S (min (h+1) S) ell (2*i+(if h < S ∧ bits h=true then 1 else 0))
private def value_type : (Nat → Bool) → Nat → Nat → Nat → Nat → Nat:=value
private theorem monotone (bits : Nat → Bool) (S h ell i : Nat) : i ≤ value bits S h ell i := by
  induction ell generalizing h i with
  | zero=>exact le_rfl
  | succ ell ih=>
    change i ≤ value bits S (min (h+1) S) ell (2*i+(if h < S ∧ bits h=true then 1 else 0))
    have lower:=ih (min (h+1) S) (2*i+(if h < S ∧ bits h=true then 1 else 0))
    omega
private theorem min_step (S h e : Nat) : min (min (h+1) S+e) S=min (h+(e+1)) S := by omega
/-- ENTIRE native BE driver, including the actual physical source shuttle
between ALL iterations. A quota cap returns the real dirty image at abortD5.
Neither the source base nor any computed operand is installed by this theorem. -/
private theorem prepared (k P m S L n Q F width ell i W h : Nat)
    (T : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (fr : Frame T S L (L+n+1) Q F) (banks : Banks T L n F width)
    (gap : L+n+1+Q+1 < F) (fit : F+5*width+n+7 ≤ P) (range : h ≤ S)
    (ellFits : ell ≤ width) (ic : i ≤ W) (wc : W ≤ width)
    (source : ∀ j,h ≤ j → j < S → T j=some (bits j))
    (carried : sourceMode m=(if h < S then if bits h then 1 else 0 else 2))
    (b0 : ∀ j,F+1 < j → j < F+width+2 → ∃ b,T j=some b)
    (b1 : ∀ j,F+width+2 < j → j < F+width+n+3 → ∃ b,T j=some b) :
    ∃ t,t ≤ (ell+1)*(512*(width+1)^2+16*(F+width+n+8)) ∧
      ((value bits S h ell i ≤ W ∧ ∃ m',m' < 144 ∧
        sourceMode m'=(if min (h+ell) S < S then if bits (min (h+ell) S) then 1 else 0 else 2) ∧
        flag m'=flag m ∧ bad m'=bad m ∧ GPath (M:=machine k) P t
          (C k 93 m (F+width+n+3) (image (hole T h S) L n F width ell i 0 (W-i)))
          (C k 183 m' (F+width+n+3)
            (image (hole T (min (h+ell) S) S) L n F width 0 (value bits S h ell i) 0 (W-value bits S h ell i)))) ∨
       (W < value bits S h ell i ∧ ∃ (e m' v out : Nat),e < ell ∧ m' < 144 ∧
        sourceMode m'=(if min (h+e) S < S then if bits (min (h+e) S) then 1 else 0 else 2) ∧
        flag m'=flag m ∧ bad m'=bad m ∧ GPath (M:=machine k) P t
          (C k 93 m (F+width+n+3) (image (hole T h S) L n F width ell i 0 (W-i)))
          (C k 213 m' (F+4*width+n+6) (image (hole T (min (h+e) S) S) L n F width (ell-e-1) v out 0)))) := by
  induction ell generalizing h i m with
  | zero=>
    have hb:=holeBanks banks (sourceLow fr) h
    have blank:=delimiters hb 0 i 0 (W-i)
    have finish:=ellDec k P m (F+width+n+3) width 0
      (image (hole T h S) L n F width 0 i 0 (W-i)) hm (by omega) (by omega)
      (blank 2 (by decide))
      (by have h:=blank 3 (by decide);convert h using 1;dsimp only [SerializedBody.delimiter];congr 1;omega)
      (by intro j lo hi;exact digit hb 0 i 0 (W-i) 2 j (by decide) (by decide) lo (by dsimp only [SerializedBody.delimiter];omega))
    refine ⟨3,?_,Or.inl ⟨ic,m,hm,?_,rfl,rfl,?_⟩⟩
    · have square : 0 < (width+1)^2:=by positivity
      nlinarith only [square,Nat.zero_le (F+width+n+8)]
    · simpa only [Nat.add_zero,Nat.min_eq_left range] using carried
    · simpa only [Nat.mul_zero,Nat.zero_add,if_pos rfl,value,Nat.add_zero,Nat.min_eq_left range] using finish
  | succ ell ih=>
    let bit:=if h < S then bits h else false
    have carriedBit : sourceMode m=1 ↔ bit=true:=by
      rw [carried]
      dsimp only [bit]
      by_cases inside : h < S
      · rw [if_pos inside,if_pos inside];cases bits h <;> decide
      · rw [if_neg inside,if_neg inside];decide
    have bitValue : (if bit then 1 else 0)=(if h < S ∧ bits h=true then 1 else 0):=by
      dsimp only [bit]
      by_cases inside : h < S
      · rw [if_pos inside];cases bits h <;> simp only [inside,true_and,if_true,if_false,Bool.false_eq_true]
      · simp only [Bool.false_eq_true,if_false,inside,false_and]
    let nextI:=2*i+(if bit then 1 else 0)
    have hb:=holeBanks banks (sourceLow fr) h
    have hb0 : ∀ j,F+1 < j → j < F+width+2 → ∃ b,hole T h S j=some b:=by
      intro j lo hi
      dsimp only [hole]
      split_ifs with inside
      · change ∃ b,(if j=h then none else T j)=some b
        rw [if_neg (by have rm:=room banks;have sl:=sourceLow fr;omega)]
        exact b0 j lo hi
      · exact b0 j lo hi
    have hb1 : ∀ j,F+width+2 < j → j < F+width+n+3 → ∃ b,hole T h S j=some b:=by
      intro j lo hi
      dsimp only [hole]
      split_ifs with inside
      · change ∃ b,(if j=h then none else T j)=some b
        rw [if_neg (by have rm:=room banks;have sl:=sourceLow fr;omega)]
        exact b1 j lo hi
      · exact b1 j lo hi
    obtain ⟨a,ap,round⟩:=arithmetic k P m L n F width (ell+1) i W (hole T h S) bit
      hm hb fit (by omega) ellFits ic wc carriedBit hb0 hb1
    have goalValue : value bits S h (ell+1) i=value bits S (min (h+1) S) ell nextI:=by
      dsimp only [value,nextI];rw [bitValue]
    rcases round with ⟨good,part⟩|⟨bad,v,out,part⟩
    · obtain ⟨b,m',bp,mb,mc,mflag,mbad,shift⟩:=advance k P m S L n Q F width ell nextI 0 (W-nextI) h T bits
        hm fr banks gap fit range source carried b0 b1
      have front:=joinPath part shift
      obtain ⟨t,tp,tail⟩:=ih (m:=m') (h:=min (h+1) S) (i:=nextI) mb (Nat.min_le_right _ _) (by omega) good
        (by intro j lo hi;exact source j (by omega) hi) mc
      have position:=min_step S h
      refine ⟨a+b+t,?_,?_⟩
      · nlinarith only [ap,bp,tp,Nat.zero_le width,Nat.zero_le (width^2),Nat.zero_le (F+width+n+8)]
      · rcases tail with ⟨valid,m'',mmb,mmc,ff,bb,path⟩|⟨invalid,e,m'',v,out,ei,mmb,mmc,ff,bb,path⟩
        · refine Or.inl ⟨by rwa [goalValue],m'',mmb,?_,ff.trans mflag,bb.trans mbad,?_⟩
          · simpa only [position] using mmc
          · simpa only [position,goalValue,Nat.add_sub_cancel,nextI] using joinPath front path
        · refine Or.inr ⟨by rwa [goalValue],e+1,m'',v,out,by omega,mmb,?_,ff.trans mflag,bb.trans mbad,?_⟩
          · simpa only [position] using mmc
          · have residual : ell+1-(e+1)-1=ell-e-1:=by omega
            simpa only [position,residual,Nat.add_sub_cancel,nextI] using joinPath front path
    · have larger:=monotone bits S (min (h+1) S) ell nextI
      refine ⟨a,?_,Or.inr ⟨?_,0,m,v,out,by omega,hm,?_,rfl,rfl,?_⟩⟩
      · nlinarith only [ap,Nat.zero_le ell,Nat.zero_le (F+width+n+8),Nat.zero_le ((width+1)^2)]
      · rw [goalValue];omega
      · simpa only [Nat.add_zero,Nat.min_eq_left range] using carried
      · simpa only [Nat.add_zero,Nat.min_eq_left range,Nat.sub_zero,Nat.add_sub_cancel] using part
#print axioms value_type
#print axioms monotone
#print axioms min_step
#print axioms prepared
end VirtualFinalClosure.GuardDriver
