import FullIngressClosure.Frame
import Complexity.PrivateInterfaceLookupInstallerFrame
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private def lookupContracts_0 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) :=
  PartAPrivateInstallerFrame.contracts
#check (lookupContracts_0 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)))
run_cmd do
  let entries ← lookupContracts_0
  PartAPrivateLookupCore.installChecked entries
  for (owner,user,_,_,_,_) in entries do
    let n := mkPrivateNameCore owner user
    let axs := (← collectAxioms n).toList
    unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "nonstandard rollout interface root"
    logInfo m!"rollout-root|{n}|axioms={axs}"
private theorem prefix_from_new {k N B t : Nat} (c : Config (CarryWindow.machine k).stateCount N B)
    (early : ∀ u,u < t → ((BodyIngress.machine k).run u (BodyIngress.config k c)).state ≠
      BodyIngress.old k (CarryWindow.ready k)) :
    ∀ u,u ≤ t → (BodyIngress.machine k).run u (BodyIngress.config k c)=
      BodyIngress.config k ((CarryWindow.machine k).run u c) := by
  intro u hu
  induction u with
  | zero => rw [UniformTM.run,UniformTM.run]
  | succ u ih =>
    have eq:=ih (by omega)
    have safe : ((CarryWindow.machine k).run u c).state ≠ CarryWindow.ready k := by
      intro bad
      apply early u (by omega)
      rw [eq]
      change BodyIngress.old k _ = _
      rw [bad]
    rw [UniformTM.run,eq,oldStep _ safe,UniformTM.run]
private theorem frame_run (k : Nat) (bodyProof : BodyIngress.Target.Body k)
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
  obtain ⟨e,price,endRun,_foot,safe,early⟩:=bodyProof R S z n p g W Q source (fun _=>false) T
    (fr_positive frame) (fr_sourceWidth frame) (fr_width frame) (fr_physical frame)
    (fr_gFits frame) (fr_wFits frame) (fr_ellFits frame) (fr_paid frame) arena
    (fr_sourceCells frame) (fr_eof frame) (fr_register frame) (fr_separator frame) right assignment
    marks gap (fr_fence frame) (fr_delimiters frame) (fr_bank0 frame) (fr_bank1 frame) (fr_bank2 frame)
    (fr_bank34 frame) (fr_bank5 frame) (fr_fresh frame) fit hd0 hh
  refine ⟨e,price,?_,safe,early⟩
  calc
    (BodyIngress.machine k).run e c=
        ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source (p+bitLength W+W))),
          ⟨S+z+2+n+1,hh⟩,fun i=>SerializedBody.prepared T S (p+bitLength W+W) F r n g W i.val⟩ := endRun
    _ = _ := by
      apply Config.ext_parts
      · rfl
      · exact Fin.ext eqH
      · rfl
private theorem segment_complete (k : Nat) (bodyProof : BodyIngress.Target.Body k)
    (R S z n p g W Q M : Nat) (source : Fin S → Bool) (I : Nat → Option Bool)
    (frame : InstallerFrame R S z n p g W Q source I)
    (mExact : M=p+bitLength W+W)
    (c : Config (BodyIngress.machine k).stateCount R (FixedRawLengthFence.allocation R))
    (t d : Nat)
    (hd0 : FixedRawLengthFence.fencePos R+1 < tapeLength R (FixedRawLengthFence.allocation R))
    (hH : S+z+n+3 < tapeLength R (FixedRawLengthFence.allocation R))
    (total : t+d ≤ 8589934592*(k+1)*(R+1)^5)
    (pre : (BodyIngress.machine k).run (t+d) c=
      ⟨BodyIngress.old k (CarryWindow.ready k),⟨FixedRawLengthFence.fencePos R+1,hd0⟩,fun i=>I i.val⟩)
    (base : Config (CarryWindow.machine k).stateCount R (FixedRawLengthFence.allocation R))
    (initialEq : BodyIngress.config k base=c)
    (first : ∀ u,u < t+d → ((BodyIngress.machine k).run u c).state ≠ BodyIngress.old k (CarryWindow.ready k))
    (priorSafe : ∀ u,u ≤ t+d → ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).accept ∧
      ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject) :
    ∃ (e : Nat) (_fit : SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 12 <
      tapeLength R (FixedRawLengthFence.allocation R)),
    e ≤ 1073741824*(R+1)^3 ∧ t+d+e ≤ 17179869184*(k+1)*(R+1)^6 ∧
    (∀ i,M ≤ i → ∀ hi : i < S,I i=some (source ⟨i,hi⟩)) ∧
    (BodyIngress.machine k).run (t+d+e) c=
      ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared I S M (FixedRawLengthFence.fencePos R) (S-p) n g W i.val⟩ ∧
    (∀ u,u < t+d+e → ∀ mode:Fin 3,((BodyIngress.machine k).run u c).state ≠ BodyIngress.body k (SerializedBody.entry mode)) ∧
    (∀ u,u ≤ t+d+e → ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).accept ∧
      ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject) := by
  have fit:=BodyIngress.workspace_room R (S-p) n (fr_positive frame)
    ((Nat.sub_le S p).trans (fr_sourceWidth frame)) (fr_width frame)
  obtain ⟨e,price,endRun,safe,early⟩:=frame_run k bodyProof R S z n p g W Q source I frame hd0 hH
  have arrived : (BodyIngress.machine k).run (t+d+e) c=
      ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared I S M (FixedRawLengthFence.fencePos R) (S-p) n g W i.val⟩ := by
    rw [UniformTM.run_add,pre]
    simpa only [mExact] using endRun
  have tx:=prefix_from_new base (t:=t+d) (by rw [initialEq]; exact first)
  have noEntry (u : Nat) (hu : u ≤ t+d) (mode : Fin 3) :
      ((BodyIngress.machine k).run u c).state ≠ BodyIngress.body k (SerializedBody.entry mode) := by
    rw [← initialEq,tx u hu]
    exact (BodyIngress.embeddings k).2.2.2.2.2.2 _ mode
  refine ⟨e,fit,price,BodyIngress.clock_slack k R t d e total price,?_,arrived,?_,?_⟩
  · intro i hl hi
    exact fr_sourceCells frame i ((Nat.le_add_right p (bitLength W)).trans
      ((Nat.le_add_right _ W).trans (by rwa [← mExact]))) hi
  · intro u hu mode
    by_cases before : u < t+d
    · exact noEntry u (Nat.le_of_lt before) mode
    · rw [show u=t+d+(u-(t+d)) by omega,UniformTM.run_add,pre]
      exact early (u-(t+d)) (by omega) mode
  · intro u hu
    by_cases before : u ≤ t+d
    · exact priorSafe u before
    · rw [show u=t+d+(u-(t+d)) by omega,UniformTM.run_add,pre]
      exact safe (u-(t+d)) (by omega)
private theorem raw_of_body (k : Nat) (bodyProof : BodyIngress.Target.Body k) : BodyIngress.Target.Raw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=BodyIngress.accepted_frontier k x w accepted
  refine ⟨pr,parsed,z,hH,gamma,eof,?_⟩
  intro phys
  obtain ⟨fit,branch⟩:=physical phys
  refine ⟨fit,?_⟩
  rcases branch with overflow | ⟨ellFits,branch⟩
  · exact Or.inl overflow
  · refine Or.inr ⟨ellFits,?_⟩
    rcases branch with normal | cap
    · obtain ⟨wFits,t,d,ht,hd,total,atW,firstW,pre,safe,first⟩:=normal
      obtain ⟨frame,mExact,_mode⟩:=accepted_frame k x w accepted pr parsed z gamma phys ellFits wFits
      obtain ⟨e,fit12,price,total',source,done,early,safe'⟩:=
        segment_complete k bodyProof _ _ z _ _ _ _ _ _ (Fin.append x w) _ frame mExact _ t d _ hH total pre
          (initialConfig (CarryWindow.machine k) _ (encodePair x w)) rfl first safe
      exact Or.inl ⟨wFits,t,d,e,ht,hd,total,atW,firstW,pre,first,fit12,price,total',source,done,early,safe'⟩
    · exact Or.inr cap
end FullIngressClosure
