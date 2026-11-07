import VirtualFinalClosure.MaskedLength
import VirtualFinalClosure.GrownFrame
import VirtualFinalClosure.WeightCapFrame
import VirtualFinalClosure.GuardLayout
namespace VirtualFinalClosure.GrownFinalImage
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residualImage",(0:Nat)),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","low","residualLow",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","capacityImage",0),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","tail","capacityTail",1),
      ("VirtualFinalClosure.MaskedLength","VirtualFinalClosure.MaskedLength","actual","maskActual",1),
      ("VirtualFinalClosure.GrownFrame","VirtualFinalClosure.GrownFrame","lower","grownLow",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualReady.Raw","VirtualReady","bank","bank",0),
      ("SmallIngress.Runtime","SmallIngress","put","put",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong whole grown source/scratch equality term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique whole grown source/scratch equality {mod}/{key}"
private theorem stream_high (U : Nat → Option Bool) (S z n A Q F i : Nat)
    (arena : S+z+n+3+Q < F) (above : F < i) (blank : U i=none) :
    Stream.Target.image U S z n A Q Q false i=none:=by
  dsimp only [Stream.Target.image]
  rw [if_neg (by omega),if_neg (by omega)]
  simp only [Bool.false_eq_true,false_and,ite_false]
  exact blank
private theorem high_blank {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R;let S:=a+m;let L:=S+z+2;let F:=3*R+2
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    ∀ i,F < i → V i=none:=by
  intro R C S L F U V i lo
  obtain ⟨cells,_short,fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨arena,_src,_end,_reg,_sep,_assn,_last,_marks,_gap,_fence⟩:=cells
  change S+z+n+3+2^n < F at arena
  by_cases old : i < tapeLength R C
  · exact fresh ⟨i,old⟩ lo
  · apply stream_high U S z n (9+2*z) (2^n) F i arena lo
    dsimp only [U,Body.extend]
    rw [dif_neg old]
private theorem residual_gap (T : Nat → Option Bool) (L n F C ell W i : Nat)
    (room : L+n+1 < F) (positive : 0 < C) (outside : ¬bank F C n i) (high : F+1 < i) :
    residualImage T L n F C ell 0 0 W 0 i=none:=by
  dsimp only [bank] at outside
  have assn : ¬(L < i ∧ i < L+n+1):=by omega
  have b1 : ¬(F+C+2 < i ∧ i < F+C+n+3):=by omega
  have b2 : ¬(F+C+n+3 < i ∧ i < F+2*C+n+4):=by omega
  have b3 : ¬(F+2*C+n+4 < i ∧ i < F+3*C+n+5):=by omega
  have b4 : ¬(F+3*C+n+5 < i ∧ i < F+4*C+n+6):=by omega
  have b5 : ¬(F+4*C+n+6 < i ∧ i < F+5*C+n+7):=by omega
  have seed : i≠F+2*C+n+5:=by omega
  have marks : ¬(F+C+n+3 < i ∧ i ≤ F+C+n+3+min (bitLength n) C):=by
    have limit:=Nat.min_le_right (bitLength n) C
    omega
  have rest : ¬((F+C+2 < i ∧ i < F+C+n+3) ∨
      (F+C+n+3 < i ∧ i < F+2*C+n+4) ∨
      (F+2*C+n+4 < i ∧ i < F+3*C+n+5) ∨
      (F+3*C+n+5 < i ∧ i < F+4*C+n+6) ∨
      (F+4*C+n+6 < i ∧ i < F+5*C+n+7)):=by
    intro hit
    rcases hit with h|h|h|h|h
    · exact b1 h
    · exact b2 h
    · exact b3 h
    · exact b4 h
    · exact b5 h
  dsimp only [residualImage,CappedWeight.Target.image]
  rw [if_neg assn,if_neg b2,if_neg b3,if_neg b4,if_neg b5]
  dsimp only [AllArityBitLength.Target.seedImage]
  rw [if_neg seed]
  dsimp only [RuntimeBitLength.Target.fullImage]
  rw [if_neg assn,if_neg b1,if_neg marks]
  dsimp only [CappedWorkspace.Target.image]
  rw [if_neg assn,if_neg rest]
  exact capacityTail T F C i (by omega)
private theorem restored (V T : Nat → Option Bool) (S L n F r C p ell W : Nat) (b : Bool)
    (room : L+n+1 < F) (source : p=S-r) (_positive : 0 < r) (inside : p < S) (sl : S < L)
    (capacity : 0 < C) (cell : T p=some b)
    (same : ∀ i,i ≤ F+1 → ¬(L < i ∧ i < L+n+1) → T i=V i)
    (assignment : ∀ i,L < i → i < L+n+1 → V i=some false)
    (fresh : ∀ i,F < i → V i=none) :
    let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
    let I:=residualImage G L n F C ell 0 0 W 0
    Cursor.Target.scratch (put I p (some b)) F C n=Cursor.Target.scratch V F C n:=by
  intro G I
  funext i
  by_cases inBank : bank F C n i
  · change (if bank F C n i then some false else _)=if bank F C n i then some false else _
    rw [if_pos inBank,if_pos inBank]
  · change (if bank F C n i then some false else _)=if bank F C n i then some false else _
    rw [if_neg inBank,if_neg inBank]
    change (if i=p then some b else I i)=V i
    by_cases hit : i=p
    · rw [if_pos hit,hit]
      exact cell.symm.trans (same p (by omega) (by omega))
    · rw [if_neg hit]
      by_cases assn : L < i ∧ i < L+n+1
      · dsimp only [I,residualImage,CappedWeight.Target.image]
        rw [if_pos assn]
        exact (congrArg some (decide_eq_false (by omega))).trans (assignment i assn.1 assn.2).symm
      · by_cases low : i ≤ F+1
        · refine (residualLow G L n F C ell 0 0 W 0 i low assn).trans ?_
          refine (grownLow (marked T F r S r) L n F r i low assn).trans ?_
          dsimp only [marked,unary,lifted]
          rw [if_neg (by omega),if_neg (by omega)]
          exact same i low assn
        · exact (residual_gap G L n F C ell W i room capacity inBank (by omega)).trans (fresh i (by omega)).symm

#print axioms stream_high
#print axioms high_blank
#print axioms residual_gap
#print axioms restored
end VirtualFinalClosure.GrownFinalImage
