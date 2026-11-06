import VirtualFinalClosure.GuardDriver
import VirtualFinalClosure.GuardEntry
namespace VirtualFinalClosure.NativeIndex
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("PostWeight.Kernel","PostWeight","Banks.mk","banksMk",3),
      ("PostWeight.Kernel","PostWeight","Banks.room","room",1),
      ("PostWeight.Kernel","PostWeight","Banks.blank","bankBlank",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.SL","sourceLow",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","occupied","occupied",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole","hole",0),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","exterior_banks","exteriorBanks",1),
      ("VirtualFinalClosure.GuardEntry","VirtualFinalClosure.GuardEntry","path","entry",1),
      ("VirtualFinalClosure.GuardDriver","VirtualFinalClosure.GuardDriver","prepared","driver",1),
      ("VirtualFinalClosure.GuardDriver","VirtualFinalClosure.GuardDriver","value","value",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
/-- The original postLength q613 endpoint is consumed by the literal native
entry AND the entire BE driver on ONE table. T is the actual incoming whole tape;
U is its explicit pre-run reconstruction at the one carried source cell. -/
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
    ∃ t,t ≤ 1+((width+2)+(n+2))+(bitLength W+1)*(512*(width+1)^2+16*(F+width+n+8)) ∧
      ((value bits S p (bitLength W) 0 ≤ W ∧ ∃ m',m' < 144 ∧
        sourceMode m'=(if min (p+bitLength W) S < S then if bits (min (p+bitLength W) S) then 1 else 0 else 2) ∧
        flag m'=flag m ∧ bad m'=bad m ∧ GPath (M:=machine k) P t
          (node (control k (tableControl k (613+93*k)) ⟨m,hm⟩) (F+1) T)
          (C k 183 m' (F+width+n+3)
            (image (hole U (min (p+bitLength W) S) S) L n F width 0 (value bits S p (bitLength W) 0) 0 (W-value bits S p (bitLength W) 0)))) ∨
       (W < value bits S p (bitLength W) 0 ∧ ∃ (e m' v out : Nat),e < bitLength W ∧ m' < 144 ∧
        sourceMode m'=(if min (p+e) S < S then if bits (min (p+e) S) then 1 else 0 else 2) ∧
        flag m'=flag m ∧ bad m'=bad m ∧ GPath (M:=machine k) P t
          (node (control k (tableControl k (613+93*k)) ⟨m,hm⟩) (F+1) T)
          (C k 213 m' (F+4*width+n+6) (image (hole U (min (p+e) S) S) L n F width (bitLength W-e-1) v out 0)))) := by
  intro U
  have sl:=sourceLow fr
  have rm:=room banks
  have same (j : Nat) (lo : S ≤ j) : U j=T j:=by
    dsimp only [U,put];rw [if_neg (by omega)]
  have frU:=protect fr (by intro j lo _hi;exact same j lo)
  have banksU : Banks U L n F width:=exteriorBanks banks (by intro j lo;exact same j (by omega))
  have original : hole U p S=T:=by
    dsimp only [hole]
    rw [if_pos inside]
    funext j
    dsimp only [U,put]
    by_cases hit : j=p
    · rw [if_pos hit];subst j;exact holeCell.symm
    · rw [if_neg hit,if_neg hit]
  have blank:=delimiters banks (bitLength W) 0 0 W
  have full:=occupied banks b0 b1 (bitLength W) 0 0 W
  rw [idempotent] at blank full
  have front:=entry k P m F width n T hm ph fit blank full
  obtain ⟨t,tp,result⟩:=driver k P m S L n Q F width (bitLength W) 0 W p U bits
    hm frU banksU gap fit inside.le ellFits (by omega) wc (by
      intro j lo hi
      dsimp only [U,put]
      by_cases hit : j=p
      · rw [if_pos hit];subst j;rfl
      · rw [if_neg hit,source j (by omega) hi])
    (by simpa only [if_pos inside] using carried)
    (by intro j lo hi;rw [same j (by omega)];exact b0 j lo hi)
    (by intro j lo hi;rw [same j (by omega)];exact b1 j lo hi)
  rw [original,Nat.sub_zero,idempotent] at result
  refine ⟨1+((width+2)+(n+2))+t,Nat.add_le_add_left tp _,?_⟩
  rcases result with ⟨valid,m',mb,mc,mf,md,path⟩|⟨invalid,e,m',v,out,ei,mb,mc,mf,md,path⟩
  · exact Or.inl ⟨valid,m',mb,mc,mf,md,joinPath front path⟩
  · exact Or.inr ⟨invalid,e,m',v,out,ei,mb,mc,mf,md,joinPath front path⟩
#print axioms prepared
end VirtualFinalClosure.NativeIndex
