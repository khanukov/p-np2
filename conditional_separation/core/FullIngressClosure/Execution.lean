import FullIngressClosure.InstallerPath
import Complexity.PrivateInterfaceLookupCoreFullIngress
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private def lookupContracts_0 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let node := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.Node
  let head := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.Node.head
  return [
    (`BodyIngress.Native, `BodyIngress.Node, `BodyIngress.Native, 0,
      ← `(Nat → Type), .anonymous),
    (`BodyIngress.Native, `BodyIngress.Node.head, `BodyIngress.Native, 2,
      ← `(∀ {k : Nat}, $node k → Nat), .anonymous),
    (`BodyIngress.Native, `BodyIngress.embedNode, `BodyIngress.Native, 2,
      ← `(∀ {k N B : Nat} (c : $node k), $head c < tapeLength N B → Config (BodyIngress.machine k).stateCount N B), .anonymous),
    (`BodyIngress.Native, `BodyIngress.Node.mk, `BodyIngress.Native, 1,
      ← `(∀ {k : Nat}, Fin (BodyIngress.machine k).stateCount → Nat → (Nat → Option Bool) → $node k), `pNode)]
private def lookupContracts_1 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let node := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.Node
  let head := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.Node.head
  let embed := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.embedNode
  let path := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.Path
  return [
    (`BodyIngress.Native, `BodyIngress.Path, `BodyIngress.Native, 0,
      ← `((k lo hi : Nat) → Nat → $node k → $node k → Prop), `PPath),
    (`BodyIngress.Native, `BodyIngress.Path.execute, `BodyIngress.Native, 3,
      ← `(∀ {k N B lo hi t : Nat} {c d : $node k}, $path k lo hi t c d → hi < tapeLength N B →
      ∀ (hc : $head c < tapeLength N B) (hd : $head d < tapeLength N B),
      (BodyIngress.machine k).run t ($embed (N := N) (B := B) c hc) = $embed (N := N) (B := B) d hd), `pExecute),
    (`BodyIngress.Native, `BodyIngress.Path.prefix_bounds, `BodyIngress.Native, 3,
      ← `(∀ {k N B lo hi t : Nat} {c d : $node k}, $path k lo hi t c d → hi < tapeLength N B →
      ∀ u, u < t → ∀ (hc : $head c < tapeLength N B),
      ((BodyIngress.machine k).run u ($embed (N := N) (B := B) c hc)).state ≠ (BodyIngress.machine k).accept ∧
      ((BodyIngress.machine k).run u ($embed (N := N) (B := B) c hc)).state ≠ (BodyIngress.machine k).reject ∧
      (∀ mode : Fin 3, ((BodyIngress.machine k).run u ($embed (N := N) (B := B) c hc)).state ≠ BodyIngress.body k (SerializedBody.entry mode)) ∧
      lo ≤ ((BodyIngress.machine k).run u ($embed (N := N) (B := B) c hc)).head.val ∧
      ((BodyIngress.machine k).run u ($embed (N := N) (B := B) c hc)).head.val ≤ hi), `pPrefix),
    (`BodyIngress.Native, `BodyIngress.Path.bounds, `BodyIngress.Native, 3,
      ← `(∀ {k lo hi t : Nat} {c d : $node k}, $path k lo hi t c d → (lo ≤ $head c ∧ $head c ≤ hi) ∧ (lo ≤ $head d ∧ $head d ≤ hi)), `pBounds)]
private def lookupContracts_2 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  return [
    (`FullIngressClosure.Initialization, `FullIngressClosure.Six, `FullIngressClosure.Initialization, 0,
      ← `((Nat → Option Bool) → Nat → Nat → Nat → Prop), .anonymous),
    (`SerializedBodyRefinement.Proof, `SerializedBodyRefinement.Unary, `SerializedBodyRefinement.Proof, 2,
      ← `((Nat → Nat) → (Nat → Option Bool) → Nat → Nat → Prop), .anonymous),
    (`FullIngressClosure.ArithmeticStage, `FullIngressClosure.initialValues, `FullIngressClosure.ArithmeticStage, 2,
      ← `(Nat → Nat → Nat → Nat → Nat), .anonymous),
    (`FullIngressClosure.SourceScan, `FullIngressClosure.Corridor, `FullIngressClosure.SourceScan, 0,
      ← `((Nat → Option Bool) → Nat → Nat → Nat → Prop), .anonymous)]
private def lookupContracts_3 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let six := PartAPrivateLookupCore.reference `FullIngressClosure.Initialization `FullIngressClosure.Six
  let unary := PartAPrivateLookupCore.reference `SerializedBodyRefinement.Proof `SerializedBodyRefinement.Unary
  let values := PartAPrivateLookupCore.reference `FullIngressClosure.ArithmeticStage `FullIngressClosure.initialValues
  let corridor := PartAPrivateLookupCore.reference `FullIngressClosure.SourceScan `FullIngressClosure.Corridor
  let arena := PartAPrivateLookupCore.reference `FullIngressClosure.SourceArena `FullIngressClosure.Arena
  let physical := PartAPrivateLookupCore.reference `FullIngressClosure.PhysicalFrame `FullIngressClosure.PhysicalFrame
  return [
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena, `FullIngressClosure.SourceArena, 0,
      ← `((Nat → Option Bool) → Nat → Nat → Nat → Prop), .anonymous),
    (`FullIngressClosure.PhysicalFrame, `FullIngressClosure.PhysicalFrame, `FullIngressClosure.PhysicalFrame, 0,
      ← `((Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop), `PhysicalFrame),
    (`FullIngressClosure.PhysicalFrame, `FullIngressClosure.PhysicalFrame.mk, `FullIngressClosure.PhysicalFrame, 1,
      ← `(∀ {T : Nat → Option Bool} {S L H F r n Q g ell W : Nat},
      $six T F r n → (∀ j, j < 6 → $unary (SerializedBody.delimiter F r n) T j ($values g ell W j)) →
      $corridor T S L H → $arena T H F Q → $physical T S L H F r n Q g ell W), `physicalMk),
    (`FullIngressClosure.PhysicalFrame, `FullIngressClosure.canonical_corridor, `FullIngressClosure.PhysicalFrame, 3,
      ← `(∀ (S z n : Nat) (T : Nat → Option Bool) (beta : Fin n → Bool),
      T S = none → (∀ i, S < i → i < S+z+2 → T i = some false) → T (S+z+2) = none →
      T (S+z+2+n+1) = none → (∀ j : Fin n, T (S+z+2+n+1-1-j.val) = some (beta j)) →
      $corridor T S (S+z+2) (S+z+2+n+1)), `canonicalCorridor)]
private def lookupContracts_4 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let path := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.Path
  let mk := PartAPrivateLookupCore.reference `BodyIngress.Native `BodyIngress.Node.mk
  let six := PartAPrivateLookupCore.reference `FullIngressClosure.Initialization `FullIngressClosure.Six
  let unary := PartAPrivateLookupCore.reference `SerializedBodyRefinement.Proof `SerializedBodyRefinement.Unary
  let values := PartAPrivateLookupCore.reference `FullIngressClosure.ArithmeticStage `FullIngressClosure.initialValues
  let arena := PartAPrivateLookupCore.reference `FullIngressClosure.SourceArena `FullIngressClosure.Arena
  let physical := PartAPrivateLookupCore.reference `FullIngressClosure.PhysicalFrame `FullIngressClosure.PhysicalFrame
  return [
    (`FullIngressClosure.PhysicalFrame, `FullIngressClosure.six_from_values, `FullIngressClosure.PhysicalFrame, 3,
      ← `(∀ (F r n : Nat) (T : Nat → Option Bool) (g ell W : Nat),
      (∀ j, j ≤ 6 → T (SerializedBody.delimiter F r n j) = none) →
      (∀ j, j < 6 → $unary (SerializedBody.delimiter F r n) T j ($values g ell W j)) →
      (∀ i, SerializedBody.delimiter F r n 6 < i → i ≤ SerializedBody.delimiter F r n 12 → T i = none) → $six T F r n), `sixFromValues),
    (`FullIngressClosure.PhysicalFrame, `FullIngressClosure.initial_fields, `FullIngressClosure.PhysicalFrame, 3,
      ← `(∀ (F r n : Nat) (T : Nat → Option Bool) (g ell W : Nat),
      (∀ i, SerializedBody.delimiter F r n 0 < i → i < SerializedBody.delimiter F r n 1 → T i = some (decide (i-SerializedBody.delimiter F r n 0 ≤ g))) →
      (∀ i, SerializedBody.delimiter F r n 1 < i → i < SerializedBody.delimiter F r n 2 → T i = some false) →
      (∀ i, SerializedBody.delimiter F r n 2 < i → i < SerializedBody.delimiter F r n 3 → T i = some (decide (i-SerializedBody.delimiter F r n 2 ≤ ell))) →
      (∀ i, SerializedBody.delimiter F r n 3 < i → i < SerializedBody.delimiter F r n 5 → i ≠ SerializedBody.delimiter F r n 4 → T i = some false) →
      (∀ i, SerializedBody.delimiter F r n 5 < i → i < SerializedBody.delimiter F r n 6 → T i = some (decide (i-SerializedBody.delimiter F r n 5 ≤ W))) →
      ∀ j, j < 6 → $unary (SerializedBody.delimiter F r n) T j ($values g ell W j)), `initialFields),
    (`FullIngressClosure.SourceArena, `FullIngressClosure.Arena.mk, `FullIngressClosure.SourceArena, 1,
      ← `(∀ {T : Nat → Option Bool} {H F Q : Nat},
      0 < Q → H+Q < F → T H = none → T F = some false →
      (∀ i, H < i → i ≤ H+Q → T i = some true) → (∀ i, H+Q < i → i < F → T i = none) → $arena T H F Q), `arenaMk),
    (`FullIngressClosure.InstallerPath, `FullIngressClosure.installer_path, `FullIngressClosure.InstallerPath, 3,
      ← `(∀ (k R S z n p g W Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool),
      S ≤ R → n ≤ R → p < S → g ≤ S-p → W ≤ S-p → bitLength n ≤ S-p →
      $physical T S (S+z+2) (S+z+2+n+1) (FixedRawLengthFence.fencePos R) (S-p) n Q g (bitLength W) W →
      (∀ i, p ≤ i → ∀ hi : i < S, T i = some (source ⟨i,hi⟩)) →
      ∃ t, t ≤ 1073741824*(R+1)^3 ∧ $path k p (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 12) t
      ($mk (BodyIngress.old k (CarryWindow.ready k)) (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 0) T)
      ($mk (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source (p+bitLength W+W))))
        (S+z+2+n+1) (SerializedBody.prepared T S (p+bitLength W+W) (FixedRawLengthFence.fencePos R) (S-p) n g W))), `installerPath)]
run_cmd do
  let entries := (← lookupContracts_0) ++ (← lookupContracts_1) ++ (← lookupContracts_2) ++ (← lookupContracts_3) ++ (← lookupContracts_4)
  PartAPrivateLookupCore.installChecked entries
  for (owner,user,_,_,_,_) in entries do
    let n := mkPrivateNameCore owner user
    let axs := (← collectAxioms n).toList
    unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "nonstandard rollout interface root"
    logInfo m!"rollout-root|{n}|axioms={axs}"
private theorem body_entry_work (k : Nat) (mode : Fin 3) :
    BodyIngress.body k (SerializedBody.entry mode) ≠ (BodyIngress.machine k).accept ∧
    BodyIngress.body k (SerializedBody.entry mode) ≠ (BodyIngress.machine k).reject := by
  have emb:=BodyIngress.embeddings k
  constructor
  · intro bad
    apply emb.2.2.2.2.2.2 (CarryWindow.machine k).accept mode
    rw [← emb.2.2.1]
    exact bad.symm
  · intro bad
    apply emb.2.2.2.2.2.2 (CarryWindow.machine k).reject mode
    rw [← emb.2.2.2.1]
    exact bad.symm
private theorem execute_interval {k R B p P h H e : Nat}
    (s q : Fin (BodyIngress.machine k).stateCount) (T U : Nat → Option Bool)
    (path : PPath k p P e (pNode s h T) (pNode q H U))
    (fit : P < tapeLength R B) (hd : h < tapeLength R B) (hh : H < tapeLength R B)
    (work : q ≠ (BodyIngress.machine k).accept ∧ q ≠ (BodyIngress.machine k).reject) :
    let c : Config (BodyIngress.machine k).stateCount R B:=⟨s,⟨h,hd⟩,fun i=>T i.val⟩
    (BodyIngress.machine k).run e c=⟨q,⟨H,hh⟩,fun i=>U i.val⟩ ∧
    (∀ u,u ≤ e → p ≤ ((BodyIngress.machine k).run u c).head.val ∧ ((BodyIngress.machine k).run u c).head.val ≤ P) ∧
    (∀ u,u ≤ e → ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).accept ∧
      ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject) ∧
    (∀ u,u < e → ∀ mode:Fin 3,((BodyIngress.machine k).run u c).state ≠ BodyIngress.body k (SerializedBody.entry mode)) := by
  intro c
  have run:=pExecute (N:=R) (B:=B) path fit hd hh
  change (BodyIngress.machine k).run e c=⟨q,⟨H,hh⟩,fun i=>U i.val⟩ at run
  have bounds : p ≤ H ∧ H ≤ P:=(pBounds path).2
  refine ⟨run,?_,?_,?_⟩
  · intro u hu
    by_cases early : u < e
    · exact (pPrefix (N:=R) (B:=B) path fit u early hd).2.2.2
    · have eq : u=e:=by omega
      subst u
      rw [run]
      exact bounds
  · intro u hu
    by_cases early : u < e
    · have h:=pPrefix (N:=R) (B:=B) path fit u early hd
      exact ⟨h.1,h.2.1⟩
    · have eq : u=e:=by omega
      subst u
      rw [run]
      exact work
  · intro u hu mode
    exact (pPrefix (N:=R) (B:=B) path fit u hu hd).2.2.1 mode
private theorem body_complete (k : Nat) : BodyIngress.Target.Body k := by
  unfold BodyIngress.Target.Body
  intro R S z n p g W Q source beta T _positiveR sourceWidth width physical
  intro r L H F B D gFits wFits ellFits paid arena sourceCells eof register separator headBlank assignment marks gap fence
    blank bank0 bank1 bank2 bank34 bank5 fresh fit hd hh c M
  have fields:=initialFields F r n T g (bitLength W) W bank0 bank1 bank2 bank34 bank5
  have six:=sixFromValues F r n T g (bitLength W) W blank fields fresh
  have corridor:=canonicalCorridor S z n T beta eof register separator headBlank assignment
  have physicalFrame : PhysicalFrame T S L H F r n Q g (bitLength W) W:=
    physicalMk six fields corridor (arenaMk paid arena headBlank fence marks gap)
  obtain ⟨e,price,path⟩:=installerPath k R S z n p g W Q source T sourceWidth width physical
    gFits wFits ellFits physicalFrame sourceCells
  obtain ⟨run,heads,safe,first⟩:=execute_interval (k:=k) (R:=R) (B:=B)
    (BodyIngress.old k (CarryWindow.ready k)) (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M)))
    T (SerializedBody.prepared T S M F r n g W) path fit hd hh (body_entry_work k (SerializedBody.sourceMode source M))
  exact ⟨e,price,run,heads,safe,first⟩
end FullIngressClosure
