import VirtualFinalClosure.ReadyGuardFrame
import VirtualFinalClosure.GuardLayout
namespace VirtualFinalClosure.GuardRestoredFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ReadyGuardFrame","VirtualFinalClosure.ReadyGuardFrame","frame","readyFrame",(1:Nat)),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","exterior_banks","exteriorBanks",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residualImage",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.SL","sourceLow",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.room","frameRoom",1),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("SmallIngress.Runtime","SmallIngress","put","put",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual restored guard-source frame term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual restored guard-source frame {mod}/{key}"
/-- The real native guard restores the unique source hole before its q238
cleanup boundary. This SAME pre-run residualImage base supplies the complete dirty
frame and physically false assignment used by cleanup, for all n including0. -/
private theorem frame (G : Nat → Option Bool) (S L n Q F C W p : Nat) (b : Bool)
    (fr : Frame G S L (L+n+1) Q F) (positive : 0 < C) (inside : p < S) (hole : G p=none) :
    let I:=residualImage G L n F C (bitLength W) 0 0 W 0
    let J:=put I p (some b)
    Frame J S L (L+n+1) Q F ∧ Banks J L n F C ∧
      (∀ i,F+1 < i → i < F+C+2 → ∃ v,J i=some v) ∧
      (∀ i,F+C+2 < i → i < F+C+n+3 → ∃ v,J i=some v) ∧
      (∀ i,L < i → i < L+n+1 → J i=some false):=by
  intro I J
  obtain ⟨frI,banks,_hole,_id,_src,b0,b1⟩:=readyFrame G S L n Q F C W p fr positive inside hole
  have sl:=sourceLow fr
  have room:=frameRoom fr
  have below : L+n+1 < F:=by omega
  have same (i : Nat) (lo : S ≤ i) : J i=I i:=by
    change (if i=p then some b else I i)=I i
    rw [if_neg (by omega)]
  refine ⟨protect frI (by intro i lo _hi;exact same i lo),exteriorBanks banks (by intro i lo;exact same i (by omega)),?_,?_,?_⟩
  · intro i lo hi
    obtain ⟨v,cell⟩:=b0 i lo hi
    exact ⟨v,(same i (by omega)).trans cell⟩
  · intro i lo hi
    obtain ⟨v,cell⟩:=b1 i lo hi
    exact ⟨v,(same i (by omega)).trans cell⟩
  · intro i lo hi
    rw [same i (by omega)]
    dsimp only [I,residualImage,CappedWeight.Target.image]
    rw [if_pos ⟨lo,hi⟩]
    exact congrArg some (decide_eq_false (by omega))
#print axioms frame
end VirtualFinalClosure.GuardRestoredFrame
