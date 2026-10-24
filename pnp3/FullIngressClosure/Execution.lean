import FullIngressClosure.InstallerPath
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.execute","pExecute"),
      ("BodyIngress.Native","BodyIngress","Path.prefix_bounds","pPrefix"),
      ("BodyIngress.Native","BodyIngress","Path.bounds","pBounds"),
      ("FullIngressClosure.InstallerPath","FullIngressClosure","installer_path","installerPath"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","PhysicalFrame","PhysicalFrame"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","PhysicalFrame.mk","physicalMk"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","canonical_corridor","canonicalCorridor"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","six_from_values","sixFromValues"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","initial_fields","initialFields"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.mk","arenaMk") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique full Config execution interface {mod}/{key}: {found.map Prod.fst}"
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
