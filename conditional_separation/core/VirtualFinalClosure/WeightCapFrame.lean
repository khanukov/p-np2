import VirtualFinalClosure.PowerSeedFrame
namespace VirtualFinalClosure.WeightCapFrame
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",(3:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","capacityImage",(0:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","low","capacityLow",(1:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","digits","capacityDigits",(1:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","tail","capacityTail",(1:Nat)),
      ("VirtualFinalClosure.WorkspaceImage","VirtualFinalClosure.WorkspaceImage","cap_banks","baseBanks",(1:Nat)),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",(0:Nat)),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",(0:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong exact dirty W-cap frame interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact dirty W-cap frame interface {mod}/{key}"
/-- Exact residual image after genuine native arithmetic. No counter-fit
premise is used for occupancy: Some false remains occupied. -/
private def residual (T : Nat → Option Bool) (L n F C v2 v3 v4 v5 d : Nat) : Nat → Option Bool :=
  CappedWeight.Target.image (AllArityBitLength.Target.seedImage
    (RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (capacityImage T F C) L n F C) L n F C) F C n)
    L n F C v2 v3 v4 v5 d
private def residual_type : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Bool:=residual
private theorem low (T : Nat → Option Bool) (L n F C v2 v3 v4 v5 d i : Nat)
    (small : i ≤ F+1) (outside : ¬(L < i ∧ i < L+n+1)) :
    residual T L n F C v2 v3 v4 v5 d i=T i := by
  dsimp only [residual,CappedWeight.Target.image,AllArityBitLength.Target.seedImage,
    RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image]
  rw [if_neg outside,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_neg outside,if_neg (by omega),if_neg (by omega),if_neg outside,if_neg (by omega)]
  exact capacityLow T F C i small
private theorem frame (T : Nat → Option Bool) (S L n Q F C v2 v3 v4 v5 d : Nat)
    (fr : Frame T S L (L+n+1) Q F) :
    Frame (residual T L n F C v2 v3 v4 v5 d) S L (L+n+1) Q F := by
  obtain ⟨sl,lh,paid,room,eof,sep,right,d0,fence,reg,_assn,marks,gap⟩:=fr
  have below : L+n+1 < F:=by omega
  let Y:=residual T L n F C v2 v3 v4 v5 d
  have same (i : Nat) (hi : i ≤ F+1) (out : ¬(L < i ∧ i < L+n+1)) : Y i=T i:=low T L n F C v2 v3 v4 v5 d i hi out
  refine frameMk sl lh paid room ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (same S (by omega) (by omega)).trans eof
  · exact (same L (by omega) (by omega)).trans sep
  · exact (same (L+n+1) (by omega) (by omega)).trans right
  · exact (same (F+1) le_rfl (by omega)).trans d0
  · exact (same F (by omega) (by omega)).trans fence
  · intro i lo hi;obtain ⟨b,cell⟩:=reg i lo hi
    exact ⟨b,(same i (by omega) (by omega)).trans cell⟩
  · intro i lo hi
    dsimp only [Y,residual,CappedWeight.Target.image]
    rw [if_pos ⟨lo,hi⟩]
    exact ⟨_,rfl⟩
  · intro i lo hi;exact (same i (by omega) (by omega)).trans (marks i lo hi)
  · intro i lo hi;exact (same i (by omega) (by omega)).trans (gap i lo hi)
private theorem banks (T : Nat → Option Bool) (L n F C v2 v3 v4 v5 d : Nat)
    (positive : 0 < C) (room : L+n+1 < F) (d0 : T (F+1)=none) :
    let Y:=residual T L n F C v2 v3 v4 v5 d
    (∀ j,j ≤ 6 → Y (SerializedBody.delimiter F C n j)=none) ∧
      (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F C n j < i → i < SerializedBody.delimiter F C n (j+1) → ∃ b,Y i=some b) := by
  intro Y
  let X:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (capacityImage T F C) L n F C) L n F C
  let Z:=AllArityBitLength.Target.seedImage X F C n
  obtain ⟨blank,occupied⟩:=baseBanks (capacityImage T F C) L n F C room (capacityDigits T F C)
    (by intro i lo _hi;exact capacityTail T F C i lo) ((capacityLow T F C (F+1) le_rfl).trans d0)
  have zb (j : Nat) (hj : j ≤ 6) : Z (SerializedBody.delimiter F C n j)=none:=by
    dsimp only [Z,AllArityBitLength.Target.seedImage]
    rw [if_neg (by interval_cases j <;> dsimp only [SerializedBody.delimiter] <;> omega)]
    exact blank j hj
  have zo (j : Nat) (hj : j < 6) (i : Nat) (lo : SerializedBody.delimiter F C n j < i)
      (hi : i < SerializedBody.delimiter F C n (j+1)) : ∃ b,Z i=some b:=by
    dsimp only [Z,AllArityBitLength.Target.seedImage]
    split_ifs with h
    · exact ⟨true,rfl⟩
    · exact occupied j hj i lo hi
  constructor
  · intro j hj
    change CappedWeight.Target.image Z L n F C v2 v3 v4 v5 d (SerializedBody.delimiter F C n j)=none
    dsimp only [CappedWeight.Target.image]
    interval_cases j <;> dsimp only [SerializedBody.delimiter] <;>
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    all_goals exact zb _ (by omega)
  · intro j hj i lo hi
    change ∃ b,CappedWeight.Target.image Z L n F C v2 v3 v4 v5 d i=some b
    dsimp only [CappedWeight.Target.image]
    split_ifs <;> first | exact ⟨_,rfl⟩ | exact zo j hj i lo hi
private theorem doubled_image (T : Nat → Option Bool) (L n F C v2 v3 v4 v5 d : Nat)
    (room : L+n+1 < F) (assn : ∀ i,L < i → i < L+n+1 → T i=some false) :
    block (doubled (residual T L n F C v2 v3 v4 v5 d) F C n) (L+1) n (some false)=capacityImage T F (2*C) := by
  funext i
  by_cases assignment : L < i ∧ i < L+n+1
  · dsimp only [block]
    rw [if_pos (by omega),capacityLow T F (2*C) i (by omega),assn i assignment.1 assignment.2]
  · dsimp only [block]
    rw [if_neg (by omega)]
    by_cases small : i ≤ F+1
    · dsimp only [doubled]
      rw [if_neg (by omega),if_neg (by omega),low T L n F C v2 v3 v4 v5 d i small assignment,capacityLow T F (2*C) i small]
    · by_cases digit : i < F+2*C+2
      · dsimp only [doubled]
        rw [if_pos (by omega)]
        exact (capacityDigits T F (2*C) i (by omega) (by omega)).symm
      · dsimp only [doubled]
        rw [if_neg (by omega),capacityTail T F (2*C) i (by omega)]
        by_cases reset : i ≤ F+5*C+n+7
        · rw [if_pos (by omega)]
        · rw [if_neg (by omega)]
          dsimp only [residual,CappedWeight.Target.image,AllArityBitLength.Target.seedImage,
            RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image]
          rw [if_neg assignment,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
            if_neg (by omega),if_neg assignment,if_neg (by omega),if_neg (by omega),if_neg assignment,if_neg (by omega)]
          exact capacityTail T F C i (by omega)
#print axioms residual_type
#print axioms low
#print axioms frame
#print axioms banks
#print axioms doubled_image
end VirtualFinalClosure.WeightCapFrame
