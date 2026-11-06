import IngressAllocation.Target
import Complexity.PrivateInterfaceLookupInstallerFrame
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  PartAPrivateLookupCore.installChecked (← PartAPrivateInstallerFrame.contracts)
set_option maxRecDepth 4000 in
private theorem installer_heads (k : Nat) (bodyProof : BodyIngress.Target.Body k)
    (R S z n p g W Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (frame : InstallerFrame R S z n p g W Q source T)
    (hd0 : FixedRawLengthFence.fencePos R+1 < tapeLength R (FixedRawLengthFence.allocation R))
    (hH : S+z+n+3 < tapeLength R (FixedRawLengthFence.allocation R)) :
    let F:=FixedRawLengthFence.fencePos R
    let B:=FixedRawLengthFence.allocation R
    let r:=S-p
    let c : Config (BodyIngress.machine k).stateCount R B:=
      ⟨BodyIngress.old k (CarryWindow.ready k),⟨F+1,hd0⟩,fun i=>T i.val⟩
    ∃ e,e ≤ 1073741824*(R+1)^3 ∧
      (BodyIngress.machine k).run e c=
        ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source (p+bitLength W+W))),
          ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared T S (p+bitLength W+W) F r n g W i.val⟩ ∧
      (∀ u,u ≤ e → p ≤ ((BodyIngress.machine k).run u c).head.val ∧
        ((BodyIngress.machine k).run u c).head.val ≤ SerializedBody.delimiter F r n 12) ∧
      (∀ u,u ≤ e → ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).accept ∧
        ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject) ∧
      (∀ u,u < e → ∀ mode:Fin 3,((BodyIngress.machine k).run u c).state ≠ BodyIngress.body k (SerializedBody.entry mode)) := by
  intro F B r c
  have eqH : (S+z+2)+n+1=S+z+n+3 := by omega
  have fit:=BodyIngress.workspace_room R r n (fr_positive frame)
    ((Nat.sub_le S p).trans (fr_sourceWidth frame)) (fr_width frame)
  change SerializedBody.delimiter F r n 12 < tapeLength R B at fit
  have hh : (S+z+2)+n+1 < tapeLength R B := by rw [eqH]; exact hH
  have arena : (S+z+2)+n+1+Q < F := by rw [eqH]; exact fr_arena frame
  have right : T ((S+z+2)+n+1)=none := by rw [eqH]; exact fr_headBlank frame
  have assignment (j : Fin n) : T ((S+z+2)+n+1-1-j.val)=some false := by
    rw [eqH]; exact fr_assignment frame j
  have marks (i : Nat) (hl : (S+z+2)+n+1 < i) (hu : i ≤ (S+z+2)+n+1+Q) : T i=some true := by
    rw [eqH] at hl hu; exact fr_marks frame i hl hu
  have gap (i : Nat) (hl : (S+z+2)+n+1+Q < i) (hu : i < F) : T i=none := by
    rw [eqH] at hl; exact fr_gap frame i hl hu
  obtain ⟨e,price,endRun,foot,safe,early⟩:=bodyProof R S z n p g W Q source (fun _=>false) T
    (fr_positive frame) (fr_sourceWidth frame) (fr_width frame) (fr_physical frame)
    (fr_gFits frame) (fr_wFits frame) (fr_ellFits frame) (fr_paid frame) arena
    (fr_sourceCells frame) (fr_eof frame) (fr_register frame) (fr_separator frame) right assignment
    marks gap (fr_fence frame) (fr_delimiters frame) (fr_bank0 frame) (fr_bank1 frame) (fr_bank2 frame)
    (fr_bank34 frame) (fr_bank5 frame) (fr_fresh frame) fit hd0 hh
  refine ⟨e,price,?_,foot,safe,early⟩
  calc
    (BodyIngress.machine k).run e c=
        ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source (p+bitLength W+W))),
          ⟨S+z+2+n+1,hh⟩,fun i=>SerializedBody.prepared T S (p+bitLength W+W) F r n g W i.val⟩ := endRun
    _ = _ := by
      apply Config.ext_parts
      · rfl
      · exact Fin.ext eqH
      · rfl
end IngressAllocation
