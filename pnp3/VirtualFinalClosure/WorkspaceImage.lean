import VirtualFinalClosure.GrownFrame
namespace VirtualFinalClosure.WorkspaceImage
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",3)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual workspace image frame {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual workspace image frame {mod}/{key}"
private theorem lower (G : Nat → Option Bool) (L n F r i : Nat)
    (small : i ≤ F+1) (outside : ¬(L < i ∧ i < L+n+1)) :
    CappedWorkspace.Target.image G L n F r i=G i := by
  dsimp only [CappedWorkspace.Target.image]
  rw [if_neg outside,if_neg (by omega)]
private theorem ready (G : Nat → Option Bool) (S L n Q F r : Nat)
    (fr : Frame G S L (L+n+1) Q F)
    (bank0 : ∀ i,F+1 < i → i < F+r+2 → G i=some true)
    (fresh : ∀ i,F+r+2 ≤ i → i ≤ F+5*r+n+7 → G i=none) :
    let X:=CappedWorkspace.Target.image G L n F r
    Frame X S L (L+n+1) Q F ∧
      (∀ i,L < i → i < L+n+1 → X i=some true) ∧
      (∀ i,F+1 < i → i < F+r+2 → X i=some true) ∧ X (F+r+2)=none ∧
      (∀ i,F+r+2 < i → i < F+r+n+3 → X i=some false) ∧ X (F+r+n+3)=none ∧
      (∀ i,F+r+n+3 < i → i < F+2*r+n+4 → X i=some false) ∧ X (F+2*r+n+4)=none := by
  intro X
  obtain ⟨sl,lh,paid,room,eof,sep,right,d0,fence,reg,assn,marks,gap⟩:=fr
  have below : L+n+1 < F := by omega
  have low (i : Nat) (hi : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) : X i=G i:=lower G L n F r i hi out
  have assign : ∀ i,L < i → i < L+n+1 → X i=some true := by
    intro i lo hi
    dsimp only [X,CappedWorkspace.Target.image]
    rw [if_pos ⟨lo,hi⟩]
  refine ⟨frameMk sl lh paid room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,assign,?_,?_,?_,?_,?_,?_⟩
  · exact (low S (by omega) (by omega)).trans eof
  · exact (low L (by omega) (by omega)).trans sep
  · exact (low (L+n+1) (by omega) (by omega)).trans right
  · exact (low (F+1) le_rfl (by omega)).trans d0
  · exact (low F (by omega) (by omega)).trans fence
  · intro i lo hi;obtain ⟨b,cell⟩:=reg i lo hi
    exact ⟨b,(low i (by omega) (by omega)).trans cell⟩
  · intro i lo hi;exact ⟨true,assign i lo hi⟩
  · intro i lo hi;exact (low i (by omega) (by omega)).trans (marks i lo hi)
  · intro i lo hi;exact (low i (by omega) (by omega)).trans (gap i lo hi)
  · intro i lo hi
    dsimp only [X,CappedWorkspace.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    exact bank0 i lo hi
  · dsimp only [X,CappedWorkspace.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    exact fresh _ le_rfl (by omega)
  · intro i lo hi
    dsimp only [X,CappedWorkspace.Target.image]
    rw [if_neg (by omega),if_pos (by omega)]
  · dsimp only [X,CappedWorkspace.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    exact fresh _ (by omega) (by omega)
  · intro i lo hi
    dsimp only [X,CappedWorkspace.Target.image]
    rw [if_neg (by omega),if_pos (by omega)]
  · dsimp only [X,CappedWorkspace.Target.image]
    rw [if_neg (by omega),if_neg (by omega)]
    exact fresh _ (by omega) (by omega)
private theorem cap_banks (G : Nat → Option Bool) (L n F r : Nat) (room : L+n+1 < F)
    (bank0 : ∀ i,F+1 < i → i < F+r+2 → G i=some true)
    (fresh : ∀ i,F+r+2 ≤ i → i ≤ F+5*r+n+7 → G i=none) (d0 : G (F+1)=none) :
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image G L n F r) L n F r
    (∀ j,j ≤ 6 → Y (SerializedBody.delimiter F r n j)=none) ∧
      (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
        i < SerializedBody.delimiter F r n (j+1) → ∃ b,Y i=some b) := by
  intro Y
  constructor
  · intro j hj
    interval_cases j <;>
      dsimp only [Y,SerializedBody.delimiter,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image] <;>
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    · exact d0
    all_goals exact fresh _ (by omega) (by omega)
  · intro j hj i lo hi
    interval_cases j <;> dsimp only [SerializedBody.delimiter] at lo hi <;>
      dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image] <;>
      split_ifs <;> first | exact ⟨_,rfl⟩ | exact ⟨true,bank0 i (by omega) (by omega)⟩
#print axioms lower
#print axioms ready
#print axioms cap_banks
end VirtualFinalClosure.WorkspaceImage
