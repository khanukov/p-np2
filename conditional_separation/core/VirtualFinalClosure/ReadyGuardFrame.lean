import VirtualFinalClosure.GuardImage
import VirtualFinalClosure.ComputedPostWeight
namespace VirtualFinalClosure.ReadyGuardFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("PostWeight.Kernel","PostWeight","Banks.mk","banksMk",3),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residImage",0),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","frame","fullFrame",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","banks","fullBanks",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","low","fullLow",1),
      ("VirtualFinalClosure.ComputedPostWeight","VirtualFinalClosure.ComputedPostWeight","overwrite","overwrite",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.SL","sourceLow",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.room","frameRoom",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.scratchStart","startBlank",1) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong exact dirty W-cap frame interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact dirty W-cap frame interface {mod}/{key}"
/-- The SAME computed-window residual supplies all physical BE frame facts.
No caller-written banks, source, n/W or run-success certificate is installed. -/
private theorem frame (T : Nat → Option Bool) (S L n Q F width W p : Nat)
    (fr : Frame T S L (L+n+1) Q F) (positive : 0 < width) (inside : p < S)
    (hole : T p=none) :
    let I:=residImage T L n F width (bitLength W) 0 0 W 0
    Frame I S L (L+n+1) Q F ∧ Banks I L n F width ∧ I p=none ∧
      image I L n F width (bitLength W) 0 0 W=I ∧
      (∀ j,p < j → j < S → I j=T j) ∧
      (∀ j,F+1 < j → j < F+width+2 → ∃ b,I j=some b) ∧
      (∀ j,F+width+2 < j → j < F+width+n+3 → ∃ b,I j=some b) := by
  intro I
  have sl:=sourceLow fr
  have rm:=frameRoom fr
  have room : L+n+1 < F:=lt_of_le_of_lt (Nat.le_add_right (L+n+1) Q) rm
  obtain ⟨blank,occupied⟩:=fullBanks T L n F width (bitLength W) 0 0 W 0 positive room (startBlank fr)
  have bi : Banks I L n F width:=by
    refine banksMk room ?_
    intro j hj
    interval_cases j <;> exact blank _ (by omega)
  refine ⟨fullFrame T S L n Q F width (bitLength W) 0 0 W 0 fr,bi,?_,?_,?_,?_,?_⟩
  · exact (fullLow T L n F width (bitLength W) 0 0 W 0 p (by omega) (by omega)).trans hole
  · dsimp only [I,residImage,image]
    exact overwrite _ L n F width (bitLength W) 0 0 W 0 (bitLength W) 0 0 W 0
  · intro j _lo hi
    exact fullLow T L n F width (bitLength W) 0 0 W 0 j (by omega) (by omega)
  · intro j lo hi
    exact occupied 0 (by decide) j lo hi
  · intro j lo hi
    exact occupied 1 (by decide) j lo hi
#print axioms frame
end VirtualFinalClosure.ReadyGuardFrame
