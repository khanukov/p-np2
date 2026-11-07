import VirtualFinalClosure.GrownFrame
import VirtualFinalClosure.GrownTail
import VirtualFinalClosure.ComputedPostWeight
namespace VirtualFinalClosure.RawSourceFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.GrownFrame","VirtualFinalClosure.GrownFrame","lower","grownLow",1),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","image_lower","imageLow",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","physical","physicalValue",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual globally blank grown exterior {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual globally blank grown exterior {mod}/{key}"
private theorem reflected_sub (S p : Nat) (h : p ≤ S) : S-(S-p)=p := by omega
private theorem source_finite (R S B i : Nat) (h : S ≤ R) (hi : i < S) : i < tapeLength R B := by
  dsimp only [tapeLength]
  omega
private theorem fence_room (R S : Nat) (h : S ≤ R) : S < 3*R+2 := by omega
/-- Literal original source after the consumed gamma header, including the
n0 tag-cell7 history. This is a pointwise consequence of the authoritative
countdown source theorem, not a new runtime source provider. -/
private theorem table_source {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R;let L:=S+z+2
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    ∀ i,9+2*z ≤ i → ∀ hi : i < S,V i=some ((Fin.append x w) ⟨i,hi⟩) := by
  intro S R C L U V i lo hi
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have finite : i < tapeLength R C:=source_finite R S C i pair hi
  dsimp only [V,Stream.Target.image]
  rw [if_neg (by omega),if_neg (by omega)]
  change U i=some ((Fin.append x w) ⟨i,hi⟩)
  dsimp only [U,Body.extend]
  rw [dif_pos finite]
  dsimp only [Body.installedTape]
  rw [if_neg (by dsimp only [L];omega)]
  dsimp only [SmallIngress.prepared]
  rw [if_neg (by omega)]
  exact Body.raw_source_after_header x w gamma (FixedRawLengthFence.resource_bounds R).1 cap.le
    ⟨i,finite⟩ (by change 8+2*z+1 ≤ i;omega) hi
/-- Exact source in the initial bitLength image AND the fixed grown pre-run G:
all cells past the header remain original, except the one actually lifted p. -/
private theorem marked_source {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (physical : min (9+2*z+2^n) (a+m) < a+m) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let p:=min (9+2*z+2^n) S;let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C)
    let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
    (∀ i,9+2*z ≤ i → ∀ hi : i < S,T i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
      G p=none ∧ ∀ i,p < i → ∀ hi : i < S,G i=some ((Fin.append x w) ⟨i,hi⟩) := by
  intro S R C L F p r U V Y T G
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have ps : p < S:=physical
  have pe : p=9+2*z+2^n:=Nat.min_eq_left (physicalValue S z n physical).le
  have pEq : S-r=p:=reflected_sub S p ps.le
  have sf : S < F:=fence_room R S pair
  have sl : S < L:=by dsimp only [L];omega
  have A_le_p : 9+2*z ≤ p:=by rw [pe];exact Nat.le_add_right _ _
  have tf (i : Nat) (lo : 9+2*z ≤ i) (hi : i < S) : T i=some ((Fin.append x w) ⟨i,hi⟩):=by
    have finite : i < tapeLength R C:=source_finite R S C i pair hi
    have low : Y i=V i:=imageLow V L n F r i
      ((hi.trans sf).le.trans (Nat.le_succ F)) (fun h=>Nat.lt_asymm (hi.trans sl) h.1)
    exact (maskedLow Y (tapeLength R C) i finite).trans (low.trans (table_source x w gamma cap i lo hi))
  have low (i : Nat) (hi : i < S) : G i=marked T F r S r i:=
    grownLow (marked T F r S r) L n F r i
      ((hi.trans sf).le.trans (Nat.le_succ F)) (fun h=>Nat.lt_asymm (hi.trans sl) h.1)
  refine ⟨tf,?_,?_⟩
  · rw [low p ps]
    dsimp only [marked,unary,lifted]
    rw [if_neg (by omega),if_pos ⟨Nat.sub_pos_of_lt ps,pEq.symm⟩]
  · intro i lo hi
    rw [low i hi]
    dsimp only [marked,unary,lifted]
    rw [if_neg (by omega),if_neg (by rw [pEq];omega)]
    exact tf i (A_le_p.trans lo.le) hi
#print axioms reflected_sub
#print axioms source_finite
#print axioms fence_room
#print axioms table_source
#print axioms marked_source
end VirtualFinalClosure.RawSourceFrame
