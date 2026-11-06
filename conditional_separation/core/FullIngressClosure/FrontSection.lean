import Complexity.PrivateInterfaceLookupResolvedInstallerPath
import FullIngressClosure.Setup
import FullIngressClosure.ArithmeticStage
import FullIngressClosure.PreparationClock
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateInstallerPath.bindings `FullIngressClosure.FrontSection
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated installer-path identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem old_ready_safe (k : Nat) : Safe k (BodyIngress.old k (CarryWindow.ready k)) := by
  have emb:=BodyIngress.embeddings k
  have ready:=readyNe k
  refine ⟨?_,?_,?_⟩
  · rw [emb.2.2.1]
    intro bad
    exact ready.1 (emb.2.2.2.2.1 bad)
  · rw [emb.2.2.2.1]
    intro bad
    exact ready.2 (emb.2.2.2.2.1 bad)
  · exact emb.2.2.2.2.2.2 _
private theorem initial_values_outside (g ell W : Nat) :
    (fun j=>if j < 6 then initialValues g ell W j else 0)=initialValues g ell W := by
  funext j
  by_cases small : j < 6
  · rw [if_pos small]
  · have j0 : j ≠ 0:=by omega
    have j2 : j ≠ 2:=by omega
    have j5 : j ≠ 5:=by omega
    dsimp only [initialValues]
    rw [if_neg small,if_neg j0,if_neg j2,if_neg j5]
private theorem installer_front_section (k R r n lo g ell W : Nat) (T : Nat → Option Bool)
    (hr : r ≤ R) (hn : n ≤ R) (hg : g ≤ r) (he : ell ≤ r) (hw : W ≤ r)
    (frame : Six T (FixedRawLengthFence.fencePos R) r n)
    (old : ∀ j,j < 6 → BankUnary (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n)
      T j (initialValues g ell W j))
    (lower : lo ≤ SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 0) :
    ∃ t,t ≤ 262144*(R+1)^2 ∧ PPath k lo
      (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12) t
      (pNode (BodyIngress.old k (CarryWindow.ready k)) (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 0) T)
      (pNode (st k 1176) (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 1)
        (arithmeticTape (stageTape T (FixedRawLengthFence.fencePos R) r n 12 0)
          (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n) g ell W)) ∧
      Registers (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n)
        (arithmeticTape (stageTape T (FixedRawLengthFence.fencePos R) r n 12 0)
          (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n) g ell W) (finalValues g ell W) := by
  let F:=FixedRawLengthFence.fencePos R
  let D:=SerializedBody.delimiter F r n
  let P:=D 12
  have upper : D 12 ≤ P:=le_rfl
  have blank : T (D 0)=none:=sixBlank frame 0 (by decide)
  have safe:=old_ready_safe k
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) (BodyIngress.old k (CarryWindow.ready k)) (st k 0)
    (D 0) (D 0) T .stay ⟨safe.1,safe.2.1⟩ safe.2.2
    ⟨lower,delimiterMono F r n 0 12 (by decide) le_rfl⟩ ⟨lower,delimiterMono F r n 0 12 (by decide) le_rfl⟩
    (by
      rw [blank,BodyIngress.table_delta,if_pos ⟨rfl,rfl⟩,stSmall k 0 (by decide)] ) rfl
  obtain ⟨t0,h0,setup⟩:=workspaceSetup T frame lower upper
  have regs:=registersAfterSetup frame (initialValues g ell W) old
  rw [initial_values_outside] at regs
  obtain ⟨t1,h1,arithmetic,final⟩:=arithmeticPrepare (k:=k) _ g ell W regs hg he hw lower upper
  have path:=pAppend first (pAppend setup arithmetic)
  refine ⟨_,?_,path,final⟩
  have price:=preparationPrice R r n g ell W t0 t1 hr hn hg he hw h0 h1
  omega
end FullIngressClosure
