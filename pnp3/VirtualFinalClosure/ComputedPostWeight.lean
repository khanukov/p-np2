import VirtualFinalClosure.PostReplay
import VirtualFinalClosure.WeightCapFrame
namespace VirtualFinalClosure.ComputedPostWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.PostReplay","VirtualFinalClosure.PostReplay","prepared","postReplay",(1:Nat)),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",(0:Nat)),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","banks","banks",(1:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",(0:Nat)),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",(0:Nat)),
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
private theorem overwrite (Z : Nat → Option Bool) (L n F C a b c d e f g h v w : Nat) :
    CappedWeight.Target.image (CappedWeight.Target.image Z L n F C a b c d e) L n F C f g h v w=
      CappedWeight.Target.image Z L n F C f g h v w := by
  funext i
  dsimp only [CappedWeight.Target.image]
  split_ifs <;> rfl
/-- The real computed-W image itself supplies every delimiter/occupancy
premise of the native tail, including preserved bank0 C. Nothing is installed
by the proof. Both old and new images refer to the SAME pre-run tape T. -/
private theorem prepared (k N B S L n Q F C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (fr : Frame T S L (L+n+1) Q F) (positive : 0 < C)
    (wr : Cursor.Target.W k n ≤ C) (fit : F+5*C+n+7 < tapeLength N B) :
    let A:=residual T L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0
    let start : Config (machine k).stateCount N B:=⟨control k (tableControl k (430+93*k)) m,⟨F+C+n+3,by omega⟩,fun i=>A i.val⟩
    ∃ t,t ≤ 4096*(Cursor.Target.W k n+1)*(F+5*C+n+8)^2 ∧
      (machine k).run t start=⟨control k (tableControl k (613+93*k)) m,⟨F+1,by omega⟩,
        fun i=>residual T L n F C (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩ ∧
      (∀ u,u ≤ t → F+1 ≤ ((machine k).run u start).head.val ∧ ((machine k).run u start).head.val ≤ F+5*C+n+7) ∧
      (∀ u,u < t → ∀ flag : Fin 144,((machine k).run u start).state≠control k (tableControl k (613+93*k)) flag) := by
  intro A start
  have copyFr:=fr
  obtain ⟨_sl,_lh,_paid,room,_,_,_,d0,_,_,_,_,_⟩:=copyFr
  have below : L+n+1 < F:=by omega
  obtain ⟨blank,occupied⟩:=banks T L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0 positive below d0
  let Z:=AllArityBitLength.Target.seedImage
    (RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (capacityImage T F C) L n F C) L n F C) F C n
  have initial : CappedWeight.Target.image A L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0=A:=
    overwrite Z L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0 0 (n^k+k) (Cursor.Target.W k n) 0 0
  have ending : CappedWeight.Target.image A L n F C (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0=
      residual T L n F C (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0:=
    overwrite Z L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0 (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0
  obtain ⟨t,tp,done,trace,first⟩:=postReplay k N B L n F C (n^k+k) (Cursor.Target.W k n) A m ph below wr blank
    (by intro i lo hi;exact occupied 0 (by decide) i lo hi)
    (by intro i lo hi;exact occupied 1 (by decide) i lo hi) fit
  rw [initial,ending] at done
  rw [initial] at trace first
  exact ⟨t,tp,done,by intro u hu;exact (trace u hu).2,first⟩
#print axioms overwrite
#print axioms prepared
end VirtualFinalClosure.ComputedPostWeight
