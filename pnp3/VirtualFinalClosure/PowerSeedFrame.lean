import VirtualFinalClosure.CapacityImage
import VirtualFinalClosure.SeedReplay
import TotalIngressClosure.SeedTotal
namespace VirtualFinalClosure.PowerSeedFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("PowerDriver.Kernel","PowerDriver","Frame","PowerFrame",2),
      ("PowerDriver.Raw","PowerDriver","prepared_seed","preparedSeed",1),
      ("TotalIngressClosure.SeedTotal","TotalIngressClosure","seed_empty","seedEmpty",1),
      ("VirtualFinalClosure.WorkspaceImage","VirtualFinalClosure.WorkspaceImage","cap_banks","capBanks",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","image",0),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","low","imageLow",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","digits","imageDigits",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","tail","imageTail",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","full_frame","fullFrame",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual computed seed frame interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual computed seed frame interface {mod}/{key}"
/-- A fixed BEFORE-RUN reference used solely to apply the old layout lemma.
Its suffix image is proved pointwise EQUAL to the already executed capacity
image; this theorem does not install any cell or assume a desired run. -/
private theorem power (T : Nat → Option Bool) (S L n Q F C : Nat)
    (fr : Frame T S L (L+n+1) Q F) (positive : 0 < C) (fits : bitLength n ≤ C) :
    PowerFrame (AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (image T F C) L n F C) L n F C) F C n) L n Q F C := by
  obtain ⟨_sl,_lh,paid,room,_s0,sep,right,d0,fence,_reg,_assn,marks,gap⟩:=fr
  have below : L+n+1 < F:=by omega
  let V : Nat → Option Bool:=fun i=>if F < i then none else T i
  have same : SuffixCap.Target.image V F C=image T F C := by
    funext i
    by_cases low : i ≤ F+1
    · rw [imageLow T F C i low]
      dsimp only [SuffixCap.Target.image,V]
      rw [if_neg (by omega)]
      by_cases last : i=F+1
      · rw [if_pos (by omega),last,d0]
      · rw [if_neg (by omega)]
    · by_cases digit : i < F+C+2
      · rw [imageDigits T F C i (by omega) digit]
        dsimp only [SuffixCap.Target.image]
        rw [if_pos (by omega)]
      · rw [imageTail T F C i (by omega)]
        dsimp only [SuffixCap.Target.image,V]
        rw [if_neg (by omega),if_pos (by omega)]
  have vLow (i : Nat) (hi : i ≤ F) : V i=T i:=by dsimp only [V];rw [if_neg (by omega)]
  have framed:=preparedSeed L n Q F C V positive fits paid room
    ((vLow L (by omega)).trans sep) ((vLow (L+n+1) (by omega)).trans right)
    (by intro i lo hi;exact (vLow i (by omega)).trans (marks i lo hi))
    (by intro i lo hi;exact (vLow i (by omega)).trans (gap i lo hi))
    ((vLow F le_rfl).trans fence)
    (by intro i lo _hi;dsimp only [V];rw [if_pos lo])
  change PowerFrame (AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage
    (CappedWorkspace.Target.image (SuffixCap.Target.image V F C) L n F C) L n F C) F C n) L n Q F C at framed
  rw [same] at framed
  exact framed
private theorem fields (T : Nat → Option Bool) (S L n Q F C : Nat)
    (fr : Frame T S L (L+n+1) Q F) (positive : 0 < C) :
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (image T F C) L n F C) L n F C
    Frame Y S L (L+n+1) Q F ∧
      (∀ j,j ≤ 6 → Y (SerializedBody.delimiter F C n j)=none) ∧
      (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F C n j < i → i < SerializedBody.delimiter F C n (j+1) → ∃ b,Y i=some b) ∧
      Y (F+2*C+n+5)=some false := by
  intro Y
  have copyFr:=fr
  obtain ⟨_sl,_lh,_paid,room,_s0,_sep,_right,d0,_fence,_reg,_assn,_marks,_gap⟩:=copyFr
  have below : L+n+1 < F:=by omega
  have b0 : image T F C (F+1)=none:=(imageLow T F C (F+1) le_rfl).trans d0
  obtain ⟨blank,occupied⟩:=capBanks (image T F C) L n F C below (imageDigits T F C)
    (by intro i lo _hi;exact imageTail T F C i lo) b0
  exact ⟨fullFrame T S L n Q F C fr,blank,occupied,seedEmpty L n F C (image T F C) below positive⟩
#print axioms power
#print axioms fields
end VirtualFinalClosure.PowerSeedFrame
