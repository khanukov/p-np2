import VirtualFinalClosure.NativeIndex
import VirtualFinalClosure.GuardFinish
namespace VirtualFinalClosure.GuardTail
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","modeBound",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","mode_preserved","modePreserved",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","flag_preserved","flagPreserved",1),
      ("VirtualFinalClosure.GuardFlags","VirtualFinalClosure.GuardFlags","bad_set","badSet",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","exterior_banks","exteriorBanks",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_bank1","holeBank1",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_bank0","holeBank0",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_banks","holeBanks",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_frame","holeFrame",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","image_frame","imageFrame",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole","hole",0),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","occupied","occupied",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.GuardDriver","VirtualFinalClosure.GuardDriver","value","value",0),
      ("VirtualFinalClosure.GuardFinishRoutes","VirtualFinalClosure.GuardFinishRoutes","bad","badRoute",1),
      ("VirtualFinalClosure.GuardFinishRoutes","VirtualFinalClosure.GuardFinishRoutes","good","goodRoute",1),
      ("VirtualFinalClosure.GuardFinish","VirtualFinalClosure.GuardFinish","prepared","finish",1),
      ("VirtualFinalClosure.NativeIndex","VirtualFinalClosure.NativeIndex","prepared","indexRun",1),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("PostWeight.Kernel","PostWeight","Banks.room","room",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.SL","sourceLow",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong complete native BE/padding term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique complete native BE/padding term {mod}/{key}"
/-- One literal native continuation q613 -> all BE digits -> all remaining
physical payload/padding -> q238/D0, with the original pre-run source restored.
Both index-overflow and legal nonzero-index paths are executed, not assumed. -/
private theorem prepared (k P m S L n Q F width W p : Nat)
    (T : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (ph : phase m=1) (fr : Frame T S L (L+n+1) Q F) (banks : Banks T L n F width)
    (gap : L+n+1+Q+1 < F) (fit : F+5*width+n+7 ≤ P)
    (inside : p < S) (holeCell : T p=none) (wc : W ≤ width) (ellFits : bitLength W ≤ width)
    (source : ∀ j,p < j → j < S → T j=some (bits j))
    (carried : sourceMode m=(if bits p then 1 else 0))
    (idempotent : image T L n F width (bitLength W) 0 0 W=T)
    (b0 : ∀ j,F+1 < j → j < F+width+2 → ∃ b,T j=some b)
    (b1 : ∀ j,F+width+2 < j → j < F+width+n+3 → ∃ b,T j=some b) :
    let U:=put T p (some (bits p))
    ∃ t m',t ≤ 1+((width+2)+(n+2))+(bitLength W+1)*(512*(width+1)^2+16*(F+width+n+8))+128*(F+width+n+8) ∧
      m' < 144 ∧ flag m'=flag m ∧
      ((value bits S p (bitLength W) 0 ≤ W ∧
        (bad m'=0 ↔ bad m=0 ∧ ∀ j,min (p+bitLength W) S ≤ j → j < S → bits j=false) ∧
        GPath (M:=machine k) P t
          (node (control k (tableControl k (613+93*k)) ⟨m,hm⟩) (F+1) T)
          (C k 238 m' (F+1) (image U L n F width 0 (value bits S p (bitLength W) 0) 0 (W-value bits S p (bitLength W) 0)))) ∨
       (W < value bits S p (bitLength W) 0 ∧ bad m'≠0 ∧
        ∃ e v out,e < bitLength W ∧ GPath (M:=machine k) P t
          (node (control k (tableControl k (613+93*k)) ⟨m,hm⟩) (F+1) T)
          (C k 238 m' (F+1) (image U L n F width (bitLength W-e-1) v out 0)))) := by
  intro U
  have sl:=sourceLow fr
  have rm:=room banks
  have same (j : Nat) (lo : S ≤ j) : U j=T j:=by
    dsimp only [U,put];rw [if_neg (by omega)]
  have frU:=protect fr (by intro j lo _hi;exact same j lo)
  have banksU:=exteriorBanks banks (by intro j lo;exact same j (by omega))
  have sourceU (j : Nat) (lo : p ≤ j) (hi : j < S) : U j=some (bits j):=by
    dsimp only [U,put]
    by_cases hit : j=p
    · rw [if_pos hit];subst j;rfl
    · rw [if_neg hit];exact source j (by omega) hi
  have b0U : ∀ j,F+1 < j → j < F+width+2 → ∃ b,U j=some b:=by
    intro j lo hi;rw [same j (by omega)];exact b0 j lo hi
  have b1U : ∀ j,F+width+2 < j → j < F+width+n+3 → ∃ b,U j=some b:=by
    intro j lo hi;rw [same j (by omega)];exact b1 j lo hi
  obtain ⟨a,ap,result⟩:=indexRun k P m S L n Q F width W p T bits hm ph fr banks gap fit inside holeCell wc ellFits source carried idempotent b0 b1
  rcases result with ⟨valid,mm,mb,mc,mf,md,path⟩|⟨invalid,e,mm,v,out,ei,mb,mc,mf,md,path⟩
  · let h:=min (p+bitLength W) S
    let i:=value bits S p (bitLength W) 0
    let A:=image (hole U h S) L n F width 0 i 0 (W-i)
    have hb:=holeBanks banksU sl h
    have bf:=delimiters hb 0 i 0 (W-i)
    have occ:=occupied hb (holeBank0 U S L n F width h rm sl b0U)
      (holeBank1 U S L n F width h rm sl b1U) 0 i 0 (W-i)
    have framed:=imageFrame (width:=width) (holeFrame frU h) 0 i 0 (W-i)
    have route:=goodRoute k P mm S L (L+n+1) Q F width n A mb framed fit bf occ
    obtain ⟨b,m',bp,bound,flagEq,clean,tail⟩:=finish k P mm S L n Q F width 0 i 0 (W-i) h U bits
      mb frU banksU gap fit (Nat.min_le_right _ _) (by intro j lo hi;exact sourceU j (by omega) hi) mc b0U b1U
    refine ⟨a+(((n+2)+(width+2))+(F-S+3))+b,m',?_,bound,flagEq.trans mf,Or.inl ⟨valid,?_,joinPath (joinPath path route) tail⟩⟩
    · omega
    · simpa only [md] using clean
  · let h:=min (p+e) S
    let A:=image (hole U h S) L n F width (bitLength W-e-1) v out 0
    have hb:=holeBanks banksU sl h
    have bf:=delimiters hb (bitLength W-e-1) v out 0
    have occ:=occupied hb (holeBank0 U S L n F width h rm sl b0U)
      (holeBank1 U S L n F width h rm sl b1U) (bitLength W-e-1) v out 0
    have framed:=imageFrame (width:=width) (holeFrame frU h) (bitLength W-e-1) v out 0
    have route:=badRoute k P mm S L (L+n+1) Q F width n A mb framed fit bf occ
    have modeSame : sourceMode (changeMode 5 mm)=sourceMode mm:=modePreserved 5 mm mb (Or.inr (Or.inl rfl))
    obtain ⟨b,m',bp,bound,flagEq,clean,tail⟩:=finish k P (changeMode 5 mm) S L n Q F width (bitLength W-e-1) v out 0 h U bits
      (modeBound _ _) frU banksU gap fit (Nat.min_le_right _ _) (by intro j lo hi;exact sourceU j (by omega) hi)
      (modeSame.trans mc) b0U b1U
    refine ⟨a+(((width+2)+(width+2)+(width+2)+(n+2)+(width+2))+(F-S+3)+1)+b,m',?_,bound,
      flagEq.trans ((flagPreserved 5 mm mb).trans mf),Or.inr ⟨invalid,?_,e,v,out,ei,joinPath (joinPath path route) tail⟩⟩
    · omega
    · intro noBad
      have impossible:=(clean.mp noBad).1
      rw [badSet] at impossible
      cases impossible
#print axioms prepared
end VirtualFinalClosure.GuardTail
