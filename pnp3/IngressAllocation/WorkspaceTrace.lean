import IngressAllocation.ArithmeticPaths
import IngressAllocation.Time
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("CappedWorkspace.Kernel","CappedWorkspace","NFrame","WorkspaceFrame"),
      ("CappedWorkspace.Kernel","CappedWorkspace","Path","WorkspacePath"),
      ("CappedWorkspace.Kernel","CappedWorkspace","Node.mk","workspaceNode"),
      ("CappedWorkspace.Kernel","CappedWorkspace","NFrame.mk","workspaceFrame"),
      ("CappedWorkspace.Kernel","CappedWorkspace","setup_entry","setupEntry"),
      ("CappedWorkspace.Kernel","CappedWorkspace","n_iteration","nIteration"),
      ("CappedWorkspace.Kernel","CappedWorkspace","n_zero","nZero"),
      ("CappedWorkspace.Kernel","CappedWorkspace","n_finish","nFinish"),
      ("CappedWorkspace.Kernel","CappedWorkspace","nimage","nImage"),
      ("CappedWorkspace.Kernel","CappedWorkspace","bankD","bankD"),
      ("CappedWorkspace.Kernel","CappedWorkspace","banks","banks"),
      ("CappedWorkspace.Kernel","CappedWorkspace","bank_frame","bankFrame"),
      ("CappedWorkspace.Kernel","CappedWorkspace","clone_stage","cloneStage"),
      ("CappedWorkspace.Kernel","CappedWorkspace","workspace_image","workspaceImage"),
      ("CappedWorkspace.Kernel","CappedWorkspace","Path.append","pathAppend"),
      ("CappedWorkspace.Kernel","CappedWorkspace","Path.execute","pathRun"),
      ("CappedWorkspace.Kernel","CappedWorkspace","Path.first","pathFirst"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.WorkspaceStage","every_head","pathHeads"),
      ("IngressAllocation.Time","IngressAllocation","first_unique","firstUnique")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique actual workspace path interface {mod}/{key}: {found.map Prod.fst}"
private theorem workspace_heads (k N B S L n Q F r : Nat) (C : Nat → Option Bool)
    (sl : S < L) (paid : 0 < Q) (room : L+n+1+Q < F)
    (eof : C S=none) (reg : ∀ i,S < i → i < L → C i=some false)
    (sep : C L=none) (assn : ∀ i,L < i → i < L+n+1 → C i=some false)
    (right : C (L+n+1)=none)
    (marks : ∀ i,L+n+1 < i → i ≤ L+n+1+Q → C i=some true)
    (gap : ∀ i,L+n+1+Q < i → i < F → C i=none)
    (fence : C F=some false) (d0 : C (F+1)=none)
    (bank0 : ∀ i,F+1 < i → i < F+r+2 → C i=some true)
    (fresh : ∀ i,F+r+2 ≤ i → i ≤ F+5*r+n+7 → C i=none)
    (fit : F+5*r+n+7 < tapeLength N B) :
    ∃ t,t ≤ 128*(n+r+1)*(F+5*r+n+9) ∧
      (Cursor.machine k).run t (⟨Cursor.rReady k,⟨S,by omega⟩,fun i=>C i.val⟩ : Config (Cursor.machine k).stateCount N B)=
        ⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i=>CappedWorkspace.Target.image C L n F r i.val⟩ ∧
      (∀ u,u < t → ((Cursor.machine k).run u
        (⟨Cursor.rReady k,⟨S,by omega⟩,fun i=>C i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 201) ∧
      (∀ u,u ≤ t → ((Cursor.machine k).run u
        (⟨Cursor.rReady k,⟨S,by omega⟩,fun i=>C i.val⟩ : Config (Cursor.machine k).stateCount N B)).head.val ≤ F+5*r+n+7) := by
  let fr : WorkspaceFrame C L n Q F r:=workspaceFrame paid room sep assn right marks gap fence d0 bank0 fresh
  have pre:=setupEntry k S L n F r C sl (by omega) eof reg sep assn right
  obtain ⟨v,_price,install⟩:=nIteration k C L n Q F r n 0 fr (by omega)
  rw [nZero] at install
  have finish:=nFinish k C L n Q F r fr
  let C0:=nImage C L n (F+r+2) n
  obtain ⟨t0,_h0,p0⟩:=cloneStage k (F+5*r+n+7) (F+1) r 0 (bankD F r n) C0 (by omega) (bankFrame C L n Q F r 0 fr (by omega))
  obtain ⟨t1,_h1,p1⟩:=cloneStage k (F+5*r+n+7) (F+1) r 1 (bankD F r n) (banks C0 F r n 1) (by omega) (bankFrame C L n Q F r 1 fr (by omega))
  obtain ⟨t2,_h2,p2⟩:=cloneStage k (F+5*r+n+7) (F+1) r 2 (bankD F r n) (banks C0 F r n 2) (by omega) (bankFrame C L n Q F r 2 fr (by omega))
  obtain ⟨t3,_h3,p3⟩:=cloneStage k (F+5*r+n+7) (F+1) r 3 (bankD F r n) (banks C0 F r n 3) (by omega) (bankFrame C L n Q F r 3 fr (by omega))
  have path:=pathAppend (pathAppend (pathAppend (pathAppend (pathAppend (pathAppend pre install) finish) p0) p1) p2) p3
  have image : banks C0 F r n 4=CappedWorkspace.Target.image C L n F r:=workspaceImage C L n F r (by omega)
  change WorkspacePath k _ _ _ (workspaceNode (Cursor.q k 201) (F+1) (banks C0 F r n 4)) at path
  rw [image] at path
  have run:=pathRun (N:=N) (B:=B) path fit
  change (Cursor.machine k).run _
    (⟨Cursor.rReady k,⟨S,by omega⟩,fun i=>C i.val⟩ : Config (Cursor.machine k).stateCount N B)=
    ⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i=>CappedWorkspace.Target.image C L n F r i.val⟩ at run
  have before:=pathFirst (N:=N) (B:=B) path fit
  have heads:=pathHeads (N:=N) (B:=B) path fit (by change S < tapeLength N B;omega)
  obtain ⟨t,price,actual,first⟩:=CappedWorkspace.workspace k N B S L n Q F r C sl paid room eof reg sep assn right marks gap fence d0 bank0 fresh fit
  have qval : (Cursor.q k 201).val=201:=Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
  have same:=firstUnique (Cursor.machine k)
    (⟨Cursor.rReady k,⟨S,by omega⟩,fun i=>C i.val⟩ : Config (Cursor.machine k).stateCount N B)
    (fun s=>s.val=201) (s:=t)
    (by rw [actual];exact qval) (by rw [run];exact qval)
    (fun u hu=>Nat.ne_of_lt (first u hu)) (fun u hu=>Nat.ne_of_lt (before u hu))
  refine ⟨t,price,actual,first,?_⟩
  rw [same]
  exact heads
end IngressAllocation
