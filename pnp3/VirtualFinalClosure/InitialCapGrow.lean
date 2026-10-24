import VirtualFinalClosure.CapGrowImage
import VirtualFinalClosure.GrowOnce
import VirtualFinalClosure.LengthGrowFrame
namespace VirtualFinalClosure.InitialCapGrow
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.CapImageFrame","VirtualFinalClosure.CapImageFrame","frame","capFrame",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protectedFrame",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","protected_image","protectedImage",1),
      ("VirtualFinalClosure.LengthGrowFrame","VirtualFinalClosure.LengthGrowFrame","marked_banks","markedBanks",1),
      ("VirtualFinalClosure.GrowOnce","VirtualFinalClosure.GrowOnce","grow_once","growOnce",1),
      ("VirtualFinalClosure.CapGrowImage","VirtualFinalClosure.CapGrowImage","erase","erase",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong real original W-cap growth term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique real original W-cap growth term {mod}/{key}"
private theorem banks (T : Nat → Option Bool) (L n F r a b c d e : Nat)
    (positive : 0<r) (room : L+n+1 < F)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F r n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
      i < SerializedBody.delimiter F r n (j+1) → ∃ v,T i=some v) :
    let I:=CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n) L n F r a b c d e
    (∀ j,j ≤ 6 → I (SerializedBody.delimiter F r n j)=none) ∧
    (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
      i < SerializedBody.delimiter F r n (j+1) → ∃ v,I i=some v):=by
  intro I
  constructor
  · intro j hj
    have base:=blank j hj
    interval_cases j
    all_goals dsimp only [SerializedBody.delimiter] at base ⊢
    all_goals dsimp only [I,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    all_goals rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    all_goals exact base
  · intro j hj i lo hi
    dsimp only [I,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    split_ifs <;> first | exact ⟨_,rfl⟩ | exact occupied j hj i lo hi
/-- ALL four actual original arithmetic-cap images feed the SAME existing
physical growth/recompute path. The old dirty counters are erased BY executed
reset/doubling, and the resulting full G is pointwise the shared raw G. -/
private theorem prepared (k P m S L n Q F r a b c d e : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (observed : seen m=1) (fr : Frame T S L (L+n+1) Q F)
    (gap : L+n+1+Q+1 < F) (positive : 0<r) (source : r < S)
    (fit : F+5*r+n+7 ≤ P)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F r n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
      i < SerializedBody.delimiter F r n (j+1) → ∃ v,T i=some v)
    (suffix : ∀ i,S-r < i → i < S → ∃ v,T i=some v) :
    let I:=CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n) L n F r a b c d e
    let A:=marked I F r S r
    let G:=block (doubled (marked T F r S r) F r n) (L+1) n (some false)
    ∃ t,t ≤ (F-(S-r)+5)+(r*(4*r+7)+2*n+14*r+27)+(F-S+3)+1 ∧
      GPath (M:=machine k) P t (C k 40 m (S-r) A)
        (node (control k (tableControl k 98) ⟨changeMeta 4 m,metaBound 4 _⟩) S G):=by
  intro I A G
  have frI:=capFrame T S L n Q F r a b c d e fr
  have frameCopy:=fr
  obtain ⟨sl,_lh,_paid,arena,_,_,_,_,_,_,_,_,_⟩:=frameCopy
  have room : L+n+1 < F:=by omega
  have framed : Frame A S L (L+n+1) Q F:=protectedFrame frI (by
    intro i lo hi
    exact protectedImage I F r S r i source lo hi)
  obtain ⟨blankI,cellsI⟩:=banks T L n F r a b c d e positive room blank occupied
  obtain ⟨blankA,cellsA⟩:=markedBanks I F r S n (by omega) blankI cellsI
  have hole : A (S-r)=none:=by
    dsimp only [A,marked,unary,lifted]
    rw [if_neg (by omega),if_pos ⟨positive,rfl⟩]
  have suffixA : ∀ i,S-r < i → i < S → ∃ v,A i=some v:=by
    intro i lo hi
    obtain ⟨v,cell⟩:=suffix i lo hi
    refine ⟨v,?_⟩
    dsimp only [A,marked,unary,lifted,I,CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    exact cell
  have width : L+n+1-L-1=n:=by omega
  obtain ⟨t,price,path,_phase,_flag⟩:=growOnce k P m S L (L+n+1) Q F (S-r) r A hm observed framed gap
    (by omega) hole suffixA positive (by simpa only [width] using fit)
    (by simpa only [width] using blankA)
    (by simpa only [width] using cellsA)
  rw [width] at price path
  rw [erase T S L n F r a b c d e room] at path
  exact ⟨t,price,path⟩
#print axioms banks
#print axioms prepared
end VirtualFinalClosure.InitialCapGrow
